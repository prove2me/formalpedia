-- Prove2me | Theorems.Thm_LehmerTotient_cohen_hagis_bound
-- name    : LehmerTotient.cohen_hagis_bound
-- status  : Open
-- author  : @fangshuming
-- created : 2026-11-26T09:22:44.978776+00:00
-- url     : https://prove2.me/theorems/640e7d21-d3b9-4f6c-ab0c-d52c0063975b
-- title:
--   A composite solution has $\omega(n)\ge 14$
-- statement:
--   Let $n>1$ be composite, and suppose that $\varphi(n)$ divides $n-1$. Then $n$ has at least fourteen distinct prime factors. This is a known theorem of Cohen and Hagis (1980), improving Lehmer's lower bound of seven prime factors.
-- source:
--   G. L. Cohen and P. Hagis, Jr., On the number of prime factors of n if φ(n) divides n−1, Nieuw Arch. Wisk. (3) 28 (1980), 177–185, https://zbmath.org/0436.10002

import Mathlib

namespace LehmerTotient
theorem cohen_hagis_bound {n : Nat} (hn : 1 < n)
    (hcomp : ¬ Nat.Prime n) (h : Nat.totient n ∣ n - 1) :
    14 ≤ (Nat.primeFactors n).card := by sorry
end LehmerTotient
