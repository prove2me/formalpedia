-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S15_c_eq_one_forces_params
-- name    : OddOrder.Peterfalvi.S15.c_eq_one_forces_params
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T15:56:17.120922+00:00
-- url     : https://prove2.me/theorems/a00e673c-f6bc-463e-a455-045a8715c511
-- title:
--   Peterfalvi (13.12): numerical elimination forcing $p=5$, $q=3$, $c=7$
-- statement:
--   Let $p,q,c$ be natural numbers and $m$ a rational number. Assume: $p,q$ prime, $3\le p$, $q\ne2$, $p\ne q$; $2q+1\le c$ and $2q\mid c-1$; $m>7/10$ if $q\ge5$; $m>8/10$ if $q\ge7$; $m>49/100$ if $q=3$ and $p\ge5$; the value formula
--
--   $$m=1-\frac1{q-1}-\frac{q-1}{q^p}+\frac1{(q-1)q^p},$$
--
--   and the bound
--
--   $$m<\frac{q\,(p^q-1)}{c\,p^{q-1}\,(p-1)}.$$
--
--   Then $p=5$, $q=3$ and $c=7$.
--
--   This is the arithmetic heart of (13.12); the remaining case is excluded structurally elsewhere.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_SAndT_Setup/OrderDetermination.lean#L571-L696

import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_Canonicalization
import Definitions.Def_OddOrder_Peterfalvi_S13_ElementaryAbelianKernel
import Definitions.Def_OddOrder_BG_Ch2_Uniqueness_S07_Theorem74

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise IsMulCommutative

variable {G : Type*} [Group G]

theorem c_eq_one_forces_params {p q c : ℕ} {m : ℚ}
    (hp : p.Prime) (hq : q.Prime) (hp3 : 3 ≤ p) (hq2 : q ≠ 2) (hpq : p ≠ q)
    (hc2q1 : 2 * q + 1 ≤ c) (h2q : 2 * q ∣ c - 1)
    (hm5 : 5 ≤ q → (7 : ℚ) / 10 < m) (hm7 : 7 ≤ q → (8 : ℚ) / 10 < m)
    (hm49 : q = 3 → 5 ≤ p → (49 : ℚ) / 100 < m)
    (hmval : m = 1 - 1 / ((q : ℚ) - 1) - ((q : ℚ) - 1) / (q : ℚ) ^ p
      + 1 / (((q : ℚ) - 1) * (q : ℚ) ^ p))
    (hbound : m < (q : ℚ) * ((p : ℚ) ^ q - 1)
      / ((c : ℚ) * (p : ℚ) ^ (q - 1) * ((p : ℚ) - 1))) :
    p = 5 ∧ q = 3 ∧ c = 7 := by sorry

end OddOrder.Peterfalvi.S15
