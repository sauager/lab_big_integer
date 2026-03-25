#include "big_integer.h"
#include <algorithm>
#include <utility>
#include <stdexcept>

long long BigInteger::mod(long long x, long long y) const {
    return ((x % y) + y) % y;
}

BigInteger::BigInteger() : negative_(false) {
    digits_.push_back(0);
}

BigInteger::BigInteger(int value) : negative_(value < 0) {
    long long num = std::abs((long long)value);
    do {
        digits_.push_back(mod(num, 10));
        num /= 10;
    } while (num > 0);
}

BigInteger::BigInteger(long long value) : negative_(value < 0) {
    long long num = std::abs(value);
    do {
        digits_.push_back(mod(num, 10));
        num /= 10;
    } while (num > 0);
}

BigInteger::BigInteger(const std::string& str) : negative_(false) {
    size_t pos = 0;

    if (str[0] == '-' || str[0] == '+') {
        negative_ = (str[0] == '-');
        pos = 1;
    }

    while (pos + 1 < str.size() && str[pos] == '0') {
        ++pos;
    }

    for (size_t i = str.size(); i > pos; --i) {
        digits_.push_back(str[i - 1] - '0');
    }
}

bool BigInteger::is_negative() const {
    return negative_;
}

std::ostream& operator<<(std::ostream& os, const BigInteger& val) {
    if (val.negative_ && !val.is_zero()) {
        os << '-';
    }
    for (int i = (int)val.digits_.size() - 1; i >= 0; --i) {
        os << val.digits_[i];
    }
    return os;
}

std::istream& operator>>(std::istream& is, BigInteger& val) {
    val.digits_.clear();
    std::string input;
    size_t pos = 0;

    if (!(is >> input)) return is;

    val.negative_ = false;

    if (input[0] == '-') {
        val.negative_ = true;
        ++pos;
    } else if (input[0] == '+') {
        ++pos;
    }

    while (pos < input.size() - 1 && input[pos] == '0') {
        ++pos;
    }

    for (size_t i = input.size(); i > pos; --i) {
        val.digits_.push_back(input[i - 1] - '0');
    }

    return is;
}

BigInteger BigInteger::operator-() const {
    BigInteger tmp = *this;
    if (!tmp.is_zero()) {
        tmp.negative_ = !tmp.negative_;
    }
    return tmp;
}

bool BigInteger::operator<(const BigInteger& rhs) const {
    if (is_zero() && rhs.is_zero()) return false;

    if (negative_ != rhs.negative_) {
        return negative_;
    }

    if (digits_.size() != rhs.digits_.size()) {
        return negative_ ? digits_.size() > rhs.digits_.size()
                         : digits_.size() < rhs.digits_.size();
    }

    for (int i = (int)digits_.size() - 1; i >= 0; --i) {
        if (digits_[i] != rhs.digits_[i]) {
            return negative_ ? digits_[i] > rhs.digits_[i]
                             : digits_[i] < rhs.digits_[i];
        }
    }
    return false;
}

bool BigInteger::operator<=(const BigInteger& rhs) const { return !(rhs < *this); }
bool BigInteger::operator>(const BigInteger& rhs) const { return rhs < *this; }
bool BigInteger::operator>=(const BigInteger& rhs) const { return !(*this < rhs); }
bool BigInteger::operator==(const BigInteger& rhs) const { return !(*this < rhs || rhs < *this); }
bool BigInteger::operator!=(const BigInteger& rhs) const { return !(*this == rhs); }

void BigInteger::absSum(const BigInteger& other) {
    size_t max_len = std::max(digits_.size(), other.digits_.size());
    int carry = 0;

    for (size_t i = 0; i < max_len; ++i) {
        int d1 = (i < digits_.size() ? digits_[i] : 0);
        int d2 = (i < other.digits_.size() ? other.digits_[i] : 0);

        if (i < digits_.size()) {
            digits_[i] = mod(d1 + d2 + carry, 10);
        } else {
            digits_.push_back(mod(d1 + d2 + carry, 10));
        }

        carry = (d1 + d2 + carry) / 10;
    }

    if (carry) digits_.push_back(1);
}

void BigInteger::absSub(const BigInteger& other) {
    size_t max_len = std::max(digits_.size(), other.digits_.size());
    int borrow = 0;

    for (size_t i = 0; i < max_len; ++i) {
        int d1 = (i < digits_.size() ? digits_[i] : 0);
        int d2 = (i < other.digits_.size() ? other.digits_[i] : 0);

        if (i < digits_.size()) {
            digits_[i] = mod(d1 - d2 - borrow, 10);
        } else {
            digits_.push_back(mod(d1 - d2 - borrow, 10));
        }

        borrow = (d1 - d2 - borrow) < 0;
    }

    for (int i = (int)digits_.size() - 1; i > 0; --i) {
        if (digits_[i] == 0) digits_.pop_back();
        else break;
    }
}

void BigInteger::absMul(const BigInteger& other) {
    if (is_zero() || other.is_zero()) {
        digits_ = {0};
        return;
    }

    int len1 = digits_.size();
    int len2 = other.digits_.size();
    std::vector<int> result(len1 + len2, 0);

    for (int i = 0; i < len1; ++i) {
        long long carry = 0;

        for (int j = 0; j < len2 || carry > 0; ++j) {
            long long cur = result[i + j] + carry;

            if (j < len2) {
                cur += 1LL * digits_[i] * other.digits_[j];
            }

            result[i + j] = (int)(cur % 10);
            carry = cur / 10;
        }
    }

    while (result.size() > 1 && result.back() == 0) {
        result.pop_back();
    }

    digits_ = result;
}

void BigInteger::absDiv(const BigInteger& other) {
    if (other.is_zero()) throw std::invalid_argument("Division by zero");

    int n = digits_.size();
    std::vector<int> result(n, 0);
    BigInteger remainder("0");

    for (int i = n - 1; i >= 0; --i) {
        remainder.digits_.insert(remainder.digits_.begin(), digits_[i]);

        while (remainder.digits_.size() > 1 && remainder.digits_.back() == 0) {
            remainder.digits_.pop_back();
        }

        int digit = 0;
        BigInteger temp = remainder;

        while (!(temp.abs() < other.abs())) {
            temp.absSub(other);
            ++digit;
        }

        remainder = temp;
        result[i] = digit;
    }

    while (result.size() > 1 && result.back() == 0) {
        result.pop_back();
    }

    digits_ = result;
}

BigInteger& BigInteger::operator+=(const BigInteger& rhs) {
    if (negative_ == rhs.negative_) {
        absSum(rhs);
    } else if (abs() < rhs.abs()) {
        BigInteger tmp = rhs;
        std::swap(*this, tmp);
        absSub(tmp);
        negative_ = rhs.negative_;
    } else {
        absSub(rhs);
    }

    if (is_zero()) negative_ = false;
    return *this;
}

BigInteger& BigInteger::operator-=(const BigInteger& rhs) {
    return *this += (-rhs);
}

BigInteger& BigInteger::operator*=(const BigInteger& rhs) {
    if (is_zero() || rhs.is_zero()) {
        *this = BigInteger(0);
        return *this;
    }

    absMul(rhs);
    negative_ = (negative_ != rhs.negative_);
    return *this;
}

BigInteger& BigInteger::operator/=(const BigInteger& rhs) {
    absDiv(rhs);
    negative_ = (negative_ != rhs.negative_);

    if (is_zero()) negative_ = false;
    return *this;
}

BigInteger& BigInteger::operator%=(const BigInteger& rhs) {
    *this = *this - (*this / rhs) * rhs;

    if (is_zero()) negative_ = false;
    return *this;
}

BigInteger BigInteger::operator+(const BigInteger& rhs) const { return BigInteger(*this) += rhs; }
BigInteger BigInteger::operator-(const BigInteger& rhs) const { return BigInteger(*this) -= rhs; }
BigInteger BigInteger::operator*(const BigInteger& rhs) const { return BigInteger(*this) *= rhs; }
BigInteger BigInteger::operator/(const BigInteger& rhs) const { return BigInteger(*this) /= rhs; }
BigInteger BigInteger::operator%(const BigInteger& rhs) const { return BigInteger(*this) %= rhs; }

BigInteger& BigInteger::operator++() { return *this += BigInteger(1); }
BigInteger BigInteger::operator++(int) { BigInteger tmp = *this; ++(*this); return tmp; }
BigInteger& BigInteger::operator--() { return *this -= BigInteger(1); }
BigInteger BigInteger::operator--(int) { BigInteger tmp = *this; --(*this); return tmp; }

BigInteger BigInteger::abs() const {
    BigInteger tmp = *this;
    tmp.negative_ = false;
    return tmp;
}

bool BigInteger::is_zero() const {
    return digits_.size() == 1 && digits_[0] == 0;
}

std::string BigInteger::to_string() const {
    std::string res;

    if (negative_ && !is_zero()) res += "-";

    for (int i = (int)digits_.size() - 1; i >= 0; --i) {
        res += char(digits_[i] + '0');
    }

    return res;
}

BigInteger::operator bool() const {
    return !is_zero();
}