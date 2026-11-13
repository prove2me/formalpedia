-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S15_caseB_order_x_absurd_of_ge
-- name    : OddOrder.Peterfalvi.S15.caseB_order_x_absurd_of_ge
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T15:55:50.048218+00:00
-- url     : https://prove2.me/theorems/6dc3f837-3c37-414a-b4a3-c2ca642e5cea
-- title:
--   Peterfalvi (13.15): numerical elimination of the case $x\ge 2q+1$
-- statement:
--   Let $p,q,x,u$ be natural numbers and $m$ a rational number. Assume: $p,q$ are prime, $3\le p$, $q\ne2$, $p\ne q$; $2q+1\le x$; $u\,x=\dfrac{p^q-1}{p-1}$ (natural-number division); $u\ne1$ and $q\nmid u$; $m>7/10$ if $q\ge5$ and $m>8/10$ if $q\ge7$; if $q=3$ then $\dfrac{p^2-1}{6}<u$; and the analytic inequality
--
--   $$m<\frac{q\,(p^q-1)}{p^{q-1}\,x\,(p-1)}$$
--
--   holds in $\mathbb Q$. Then a contradiction follows: the conclusion is `False`.
--
--   This is the side-agnostic numerical engine for eliminating $x\ge2q+1$ in (13.15), combining the analytic inequality (13.10), (13.12) with the (13.11) bounds.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_SAndT_Setup/CaseBOrder.lean#L44-L150

import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_Canonicalization
import Definitions.Def_OddOrder_Peterfalvi_S13_ElementaryAbelianKernel
import Definitions.Def_OddOrder_BG_Ch2_Uniqueness_S07_Theorem74

namespace OddOrder.Peterfalvi.S15

variable {G : Type*} [Group G]

theorem caseB_order_x_absurd_of_ge {p q x u : ℕ} {m : ℚ}
    (hp : p.Prime) (hq : q.Prime) (hp3 : 3 ≤ p) (hq2 : q ≠ 2) (hpq : p ≠ q)
    (hx : 2 * q + 1 ≤ x)
    (hux : u * x = (p ^ q - 1) / (p - 1))
    (hu_ne_one : u ≠ 1) (hu_cop_q : ¬ q ∣ u)
    (hm5 : 5 ≤ q → (7 : ℚ) / 10 < m) (hm7 : 7 ≤ q → (8 : ℚ) / 10 < m)
    (h11c : q = 3 → ((p : ℚ) ^ 2 - 1) / 6 < (u : ℚ))
    (hanalytic : m < (q : ℚ) * ((p : ℚ) ^ q - 1)
      / ((p : ℚ) ^ (q - 1) * (x : ℚ) * ((p : ℚ) - 1))) :
    False := by sorry

end OddOrder.Peterfalvi.S15
