-- Prove2me | Theorems.Thm_ModularCurve_exists_variableChange_veluQuotient2_tateLaurent_eq_and_vcXInv_velu2X_toricPoint_eq_of_isPrimitiveRoot
-- name    : ModularCurve.exists_variableChange_veluQuotient2_tateLaurent_eq_and_vcXInv_velu2X_toricPoint_eq_of_isPrimitiveRoot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/210e891e-fb9f-51d8-a4bc-121ff943bb1d
-- title:
--   Vélu μ₂-quotient of the Tate curve: E_{q^m}/⟨ T⟩≅ E_q^{2m}
-- statement:
--   Let $K$ be a field, $N$ a nonzero natural number, and $\zeta\in K$ a primitive $N$-th root of unity, with $2\mid N$; let $m$ be a nonzero natural number. Write $E^{(k)}$ for the Tate curve $\langle 1,0,0,a_4,a_6\rangle$ over $\mathbb{Z}[[q]]$ base-changed to $K((q))$ and then pushed through the ring homomorphism `qExpand K k`, which substitutes $q\mapsto q^k$ (it shifts Hahn-series exponents by multiplication by $k$); write $P_k(c)=$ `toricPoint K k c` for the explicit pair of power series in $q$ with constant terms $c/(1-c)^2$ and $c^2/(1-c)^3$ and higher coefficients given by the divisor sums in the definition, i.e. the toric point with parameter $c$ on $E^{(k)}$. Then there exists a Weierstrass variable change $C=(u,r,s,t)$ over $K((q))$ such that, first, $C$ acting on the Vélu order-two quotient curve of $E^{(m)}$ at $P_m(-1)$ — the curve with the same $a_1,a_2,a_3$ and with $a_4,a_6$ replaced by $a_4-5g$ and $a_6-b_2g-7x_0g$, where $g=3x_0^2+2a_2x_0+a_4-a_1y_0$ at $(x_0,y_0)=P_m(-1)$ — equals $E^{(2m)}$; and second, for every natural $n$ with $(\zeta^n)^2\ne 1$, applying Vélu's order-two coordinate maps $x\mapsto x+g/(x-x_0)$ and $(x,y)\mapsto y-g\,(a_1(x-x_0)+y-y_0)/(x-x_0)^2$ to $P_m(\zeta^n)$ and then the inverse substitutions $x\mapsto u^{-2}(x-r)$, $(x,y)\mapsto u^{-3}(y-t-s(x-r))$ of $C$ yields exactly the two coordinates of $P_{2m}((\zeta^n)^2)$.
--
--   This is the $\mu_2$-step for Tate curves: the quotient of $E_{q^m}$ by its toric point of order two is, after a change of coordinates, the Tate curve $E_{q^{2m}}$, and on toric points the isogeny is $u\mapsto u^2$; the hypotheses on $\zeta$ make the statement available in every characteristic not dividing $N$, in particular away from $2$. It is used in the computation of the $j$-invariant of cyclic quotients of the Tate curve over a base change, via [`ModularCurve.cyclicQuotientJ_tateLaurent_baseChange_eq_jqNModC_of_le_zmultiples`](thm.html#ModularCurve.cyclicQuotientJ_tateLaurent_baseChange_eq_jqNModC_of_le_zmultiples).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_variableChange_veluQuotient2_tateLaurent_eq_and_vcXInv_velu2X_toricPoint_eq_of_isPrimitiveRoot.lean

import Mathlib
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_WeierstrassCurve_VeluOrderTwo
import Definitions.Def_WeierstrassCurve_VeluPointMap2
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open WeierstrassCurve
open ModularCurve

universe u

theorem ModularCurve.exists_variableChange_veluQuotient2_tateLaurent_eq_and_vcXInv_velu2X_toricPoint_eq_of_isPrimitiveRoot
    (K : Type u) [Field K] (N : ℕ) [NeZero N] (ζ : K) (hζ : IsPrimitiveRoot ζ N) (h2N : 2 ∣ N) (m : ℕ) [NeZero m] :
    ∃ C : WeierstrassCurve.VariableChange (LaurentSeries K),
      C • ((tateLaurent K).map (qExpand K m)).veluQuotient2 (toricPoint K m (-1)).1 (toricPoint K m (-1)).2 =
        (tateLaurent K).map (qExpand K (m * 2)) ∧
      ∀ n : ℕ, (ζ ^ n) ^ 2 ≠ 1 →
        WeierstrassCurve.Affine.vcXInv C
            (((tateLaurent K).map (qExpand K m)).velu2X (toricPoint K m (-1)).1 (toricPoint K m (-1)).2
              (toricPoint K m (ζ ^ n)).1) =
          (toricPoint K (m * 2) ((ζ ^ n) ^ 2)).1 ∧
        WeierstrassCurve.Affine.vcYInv C
            (((tateLaurent K).map (qExpand K m)).velu2X (toricPoint K m (-1)).1 (toricPoint K m (-1)).2
              (toricPoint K m (ζ ^ n)).1)
            (((tateLaurent K).map (qExpand K m)).velu2Y (toricPoint K m (-1)).1 (toricPoint K m (-1)).2
              (toricPoint K m (ζ ^ n)).1 (toricPoint K m (ζ ^ n)).2) =
          (toricPoint K (m * 2) ((ζ ^ n) ^ 2)).2 := by sorry
