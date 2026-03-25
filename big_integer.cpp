#include "big_integer.h"
#include <algorithm>
#include <utility>
#include <stdexcept>

long long BigInteger::mod(long long x, long long y) const {
    long long r = x % y;
    return (r < 0) ? r + y : r;
}

BigInteger::BigInteger() : negative_(false) {
    digits_.push_back(0);
}

BigInteger::BigInteger(int value) : negative_(value < 0) {
    long long v = std::abs((long long)value);
    do {
        digits_.push_back(mod(v, 10));
        v /= 10;
    } while (v > 0);
}

BigInteger::BigInteger(long long value) : negative_(value < 0) {
    long long v = std::abs(value);
    do {
        digits_.push_back(mod(v, 10));
        v /= 10;
    } while (v > 0);
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

    for (size_t i = str.size(); i-- > pos;) {
        digits_.push_back(str[i] - '0');
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
    std::string s;

    if (!(is >> s)) return is;

    size_t pos = 0;
    val.negative_ = false;

    if (s[0] == '-') {
        val.negative_ = true;
        ++pos;
    } else if (s[0] == '+') {
        ++pos;
    }

    while (pos < s.size() - 1 && s[pos] == '0') {
        ++pos;
    }

    for (size_t i = s.size(); i-- > pos;) {
        val.digits_.push_back(s[i] - '0');
    }

    return is;
}

BigInteger BigInteger::operator-() const {
    BigInteger res = *this;
    if (!res.is_zero()) {
        res.negative_ = !res.negative_;
    }
    return res;
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
    size_t n = std::max(digits_.size(), other.digits_.size());
    int carry = 0;

    for (size_t i = 0; i < n || carry; ++i) {
        if (i == digits_.size()) {
            digits_.push_back(0);
        }

        int a = digits_[i];
        int b = (i < other.digits_.size() ? other.digits_[i] : 0);

        int sum = a + b + carry;
        digits_[i] = sum % 10;
        carry = sum / 10;
    }
}

void BigInteger::absSub(const BigInteger& other) {
    int borrow = 0;

    for (size_t i = 0; i < digits_.size(); ++i) {
        int a = digits_[i];
        int b = (i < other.digits_.size() ? other.digits_[i] : 0);

        int cur = a - b - borrow;
        if (cur < 0) {
            cur += 10;
            borrow = 1;
        } else {
            borrow = 0;
        }

        digits_[i] = cur;
    }

    while (digits_.size() > 1 && digits_.back() == 0) {
        digits_.pop_back();
    }
}

void BigInteger::absMul(const BigInteger& other) {
    if (is_zero() || other.is_zero()) {
        digits_ = {0};
        return;
    }

    std::vector<int> result(digits_.size() + other.digits_.size(), 0);

    for (size_t i = 0; i < digits_.size(); ++i) {
        int carry = 0;

        for (size_t j = 0; j < other.digits_.size() || carry; ++j) {
            long long cur = result[i + j] + carry;

            if (j < other.digits_.size()) {
                cur += 1LL * digits_[i] * other.digits_[j];
            }

            result[i + j] = cur % 10;
            carry = cur / 10;
        }
    }

    while (result.size() > 1 && result.back() == 0) {
        result.pop_back();
    }

    digits_ = result;
}

void BigInteger::absDiv(const BigInteger& other) {
    if (other.is_zero()) {
        throw std::invalid_argument("Division by zero");
    }

    int n = digits_.size();
    std::vector<int> result(n, 0);
    BigInteger rem("0");

    for (int i = n - 1; i >= 0; --i) {
        rem.digits_.insert(rem.digits_.begin(), digits_[i]);

        while (rem.digits_.size() > 1 && rem.digits_.back() == 0) {
            rem.digits_.pop_back();
        }

        int q = 0;
        BigInteger temp = rem;

        while (!(temp.abs() < other.abs())) {
            temp.absSub(other);
            ++q;
        }

        rem = temp;
        result[i] = q;
    }

    while (result.size() > 1 && result.back() == 0) {
        result.pop_back();
    }

    digits_ = result;
}

BigInteger& BigInteger::operator+=(const BigInteger& rhs) {
    if (negative_ == rhs.negative_) {
        absSum(rhs);
    } else {
        if (abs() < rhs.abs()) {
            BigInteger tmp = rhs;
            std::swap(*this, tmp);
            absSub(tmp);
            negative_ = rhs.negative_;
        } else {
            absSub(rhs);
        }
    }

    if (is_zero()) {
        negative_ = false;
    }

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

    if (is_zero()) {
        negative_ = false;
    }

    return *this;
}

BigInteger& BigInteger::operator%=(const BigInteger& rhs) {
    *this = *this - (*this / rhs) * rhs;

    if (is_zero()) {
        negative_ = false;
    }

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
    BigInteger res = *this;
    res.negative_ = false;
    return res;
}

bool BigInteger::is_zero() const {
    return digits_.size() == 1 && digits_[0] == 0;
}

std::string BigInteger::to_string() const {
    std::string s;

    if (negative_ && !is_zero()) {
        s += '-';
    }

    for (int i = (int)digits_.size() - 1; i >= 0; --i) {
        s += char(digits_[i] + '0');
    }

    return s;
}

BigInteger::operator bool() const {
    return !is_zero();
}