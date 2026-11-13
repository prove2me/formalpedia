-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S15_caseA_numeric_parameters
-- name    : OddOrder.Peterfalvi.S15.caseA_numeric_parameters
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T15:56:24.908683+00:00
-- url     : https://prove2.me/theorems/3846b6ce-838c-4a4d-80b8-80ad8ac7d1ea
-- title:
--   Peterfalvi (13.13), numeric core: the estimates force $q=3$ and $u=(p-1)^2/4$
-- statement:
--   Let $p, q, u$ be natural numbers and $m$ a rational number. Assume:
--
--   - $3 \le p$, $q$ is prime and $q \ne 2$, and $2 \mid p-1$;
--   - if $q \ge 5$ then $m > 7/10$;
--   - if $q = 3$ then $(p^2-1)/6 < u$ (with $p^2-1$ computed in $\mathbb{N}$ and then cast to $\mathbb{Q}$);
--   - $u > m\, p^{\,q-1}/q$ in $\mathbb{Q}$;
--   - $u \mid \bigl((p-1)/2\bigr)^{q-1}$ (natural-number division).
--
--   Then
--   $$q = 3 \quad\text{and}\quad u = (p-1)^2/4 .$$
--
--   This is the purely arithmetical core of Peterfalvi (13.13): for $q \ge 5$ the divisibility bound contradicts $m > 7/10$, and for $q=3$ a proper divisor of $((p-1)/2)^2$ would be too small to satisfy (13.11.c).
--
--   **Formalization Note.** Subtraction and division in $p-1$, $(p-1)/2$, $(p-1)^2/4$ and $p^2-1$ are natural-number operations. The theorem is stated in a section with an unused variable $G$; it does not depend on any group.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_SAndT_Setup/OrderDetermination.lean#L170-L310

import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_Canonicalization
import Definitions.Def_OddOrder_Peterfalvi_S13_ElementaryAbelianKernel
import Definitions.Def_OddOrder_BG_Ch2_Uniqueness_S07_Theorem74

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise IsMulCommutative

variable {G : Type*} [Group G]

theorem caseA_numeric_parameters {p q u : ℕ} {m : ℚ}
    (hp3 : 3 ≤ p) (hqprime : q.Prime) (hqne2 : q ≠ 2)
    (hpeven : 2 ∣ p - 1)
    (hm5 : 5 ≤ q → (7 : ℚ) / 10 < m)
    (h13c : q = 3 → (((p ^ 2 - 1 : ℕ) : ℚ) / 6) < (u : ℚ))
    (hanalytic : (u : ℚ) >
      m * ((p ^ (q - 1) : ℕ) : ℚ) / (q : ℚ))
    (hdiv : u ∣ ((p - 1) / 2) ^ (q - 1)) :
    q = 3 ∧ u = (p - 1) ^ 2 / 4 := by sorry

end OddOrder.Peterfalvi.S15
