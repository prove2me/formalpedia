-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S15_numeric_bounds_of_analytic_inequality
-- name    : OddOrder.Peterfalvi.S15.numeric_bounds_of_analytic_inequality
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T15:57:38.29745+00:00
-- url     : https://prove2.me/theorems/bc83d497-7987-4632-9ee0-2ea5ecfac101
-- title:
--   Peterfalvi (13.11): elementary numerical bounds for $m$ and $u/c$
-- statement:
--   Let $G$ be a minimal simple group of odd order (`IsMinimalSimpleOdd G`), and let `hyp : Hypothesis` be the Peterfalvi (13.1) configuration for $G$: two maximal subgroups $S,T$ with $W=S\cap T=W_1W_2$ cyclic, $|W_1|=q$, $|W_2|=p$ ($p,q$ odd primes), $P=S_F$ and $Q=T_F$ the maximal nilpotent normal Hall subgroups, complements $U,V$ with $S'=PU$, $T'=QV$, $C=C_U(P)$, $D=C_V(Q)$, $|U|=uc$, $|V|=vd$, together with the associated character grids $\eta_{ij}$, $\mu_{ij}$, $\nu_{ij}$ ($i<q$, $j<p$). Assume the analytic inequality (13.10)
--
--   $$\frac{u}{c}>\frac{m\,p^{q-1}}{q}\quad(\text{in }\mathbb Q,\ m=\text{`hyp.m`}).$$
--
--   Then: if $q\ge7$ then $m>8/10$; if $q\ge5$ then $m>7/10$; and if $q=3$ then $m>49/100$ and $\dfrac{u}{c}>\dfrac{p^2-1}{6}$.
--
--   These bounds feed the numerical eliminations (13.12) and (13.15).
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_SAndT_Setup/OrderDetermination.lean#L509-L569

import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_Canonicalization
import Definitions.Def_OddOrder_Peterfalvi_S13_ElementaryAbelianKernel
import Definitions.Def_OddOrder_BG_Ch2_Uniqueness_S07_Theorem74

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise IsMulCommutative

variable {G : Type*} [Group G]

theorem numeric_bounds_of_analytic_inequality [Finite G]
    (hyp : Hypothesis (G := G))
    (h1310 : (hyp.u : ℚ) / (hyp.c : ℚ) >
      hyp.m * ((hyp.p ^ (hyp.q - 1) : ℕ) : ℚ) / (hyp.q : ℚ)) :
    (7 ≤ hyp.q → hyp.m > (8 / 10 : ℚ)) ∧
      (5 ≤ hyp.q → hyp.m > (7 / 10 : ℚ)) ∧
      (hyp.q = 3 →
        hyp.m > (49 / 100 : ℚ) ∧
          (hyp.u : ℚ) / (hyp.c : ℚ) > (((hyp.p ^ 2 - 1 : ℕ) : ℚ) / 6)) := by sorry

end OddOrder.Peterfalvi.S15
