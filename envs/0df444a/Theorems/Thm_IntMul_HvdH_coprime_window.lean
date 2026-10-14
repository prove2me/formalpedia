-- Prove2me | Theorems.Thm_IntMul_HvdH_coprime_window
-- name    : IntMul.HvdH.coprime_window
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-11T21:32:53.330335+00:00
-- url     : https://prove2.me/theorems/0ad799d5-9334-48a6-aee5-7e9abb62ded4
-- title:
--   Numbers $1+Qm$ with indices in a window of width $D$ are pairwise coprime when $D!\mid Q$
-- statement:
--   Let $D,Q,m,m'$ be natural numbers with $D!\mid Q$, $m\ne m'$ and $|m-m'|\le D$. Then
--   $$\gcd(1+Qm,\;1+Qm')=1 .$$
--   Indeed a common prime factor $p$ would divide $Q(m'-m)$ but not $Q$, hence $p\mid m'-m$, so $p\le D$ and $p\mid D!\mid Q$, a contradiction. This elementary fact replaces the use of primes in short intervals (Lemma 5.1) in the parameter selection of Harvey–van der Hoeven.
-- source:
--   Harvey, van der Hoeven, Integer multiplication in time O(n log n), Annals of Math. 193 (2021), https://hal.science/hal-02070778, Section 5.1 (Lemma 5.1 and condition (5.11)); elementary replacement

import Mathlib

namespace IntMul.HvdH
theorem coprime_window (D Q m m' : ℕ) (hQ : D.factorial ∣ Q) (hne : m ≠ m')
    (hw : m ≤ m' + D) (hw' : m' ≤ m + D) : Nat.Coprime (1 + Q * m) (1 + Q * m') := by sorry
end IntMul.HvdH
