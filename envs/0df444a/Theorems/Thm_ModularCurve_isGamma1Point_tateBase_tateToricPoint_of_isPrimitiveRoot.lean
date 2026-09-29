-- Prove2me | Theorems.Thm_ModularCurve_isGamma1Point_tateBase_tateToricPoint_of_isPrimitiveRoot
-- name    : ModularCurve.isGamma1Point_tateBase_tateToricPoint_of_isPrimitiveRoot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.700479+00:00
-- url     : https://prove2.me/theorems/8e60a0aa-22c2-51e8-9866-30a55de27af8
-- title:
--   Toric ℓ-torsion points give Γ₁(ℓ)-points on the Tate curve
-- statement:
--   Let $F$ be a field of characteristic zero, let $q$ be a nonzero natural number, let $\ell$ be a prime with $\ell \neq 2$, and let $c \in F^{\times}$ be a unit whose underlying element of $F$ is a primitive $\ell$-th root of unity. Consider the Weierstrass curve [`ModularCurve.tateBase F q`](def/ModularCurve_TateSlots.html#L46) over the Laurent series field $F((\mathsf q))$, obtained from the formal Tate curve `tateLaurent F` by applying the ring homomorphism `qExpand F q`, which multiplies all exponents of the Laurent variable by $q$. Let $(x_c, y_c) =$ `tateToricPoint F q c` be the pair of Laurent series given by the explicit $q$-expansions of the Tate parametrisation at $c$: the first component has constant coefficient $c(1-c)^{-2}$ and $m$-th coefficient $\sum_{d \mid m,\ q \mid d} (m/d)\bigl(c^{m/d} + c^{-m/d}\bigr) - 2\,[q \mid m]\,\sigma_1(m/q)$ for $m > 0$, and the second has constant coefficient $c^2(1-c)^{-3}$ and $m$-th coefficient $\sum_{d \mid m,\ q \mid d}\bigl(\binom{m/d}{2}c^{m/d} - \binom{m/d+1}{2}c^{-m/d}\bigr) + [q \mid m]\,\sigma_1(m/q)$. The conclusion is that the level datum with $x_P = x_Q = x_c$ and $y_P = y_Q = y_c$ is a $\Gamma_1(\ell)$-point of `tateBase F q`, that is: the point $(x_c, y_c)$ satisfies the affine Weierstrass equation of the curve, the division polynomial `preΨ ℓ` of the curve vanishes at $x_c$, and the two coordinate pairs of the datum agree.
--
--   This records that the toric point attached to a primitive $\ell$-th root of unity on the Tate curve over $F((\mathsf q))$ carries a $\Gamma_1(\ell)$-structure in the sense used throughout the project, the level datum being the diagonal pair $(P_c, P_c)$. It supplies the required point of order $\ell$ at the Tate cusp in the construction of étale and rigid level data at weight one, and in the computation of the $j$-invariant of such Tate points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_isGamma1Point_tateBase_tateToricPoint_of_isPrimitiveRoot.lean

import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_LevelRelabelling
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_KatzLevelPCusps
import Definitions.Def_ModularCurve_WeierstrassGamma1Pow
import Definitions.Def_ModularCurve_WeierstrassH1Pow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel
open ModularCurve
open scoped MatrixGroups

theorem ModularCurve.isGamma1Point_tateBase_tateToricPoint_of_isPrimitiveRoot
    (F : Type) [Field F] [CharZero F] (q : ℕ) [NeZero q]
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (c : Fˣ) (hc : IsPrimitiveRoot (c : F) ℓ) :
    ModularCurve.IsGamma1Point (ModularCurve.tateBase F q) ℓ
      (⟨(ModularCurve.tateToricPoint F q c).1, (ModularCurve.tateToricPoint F q c).2,
        (ModularCurve.tateToricPoint F q c).1, (ModularCurve.tateToricPoint F q c).2⟩ : ModularCurve.LevelPData (LaurentSeries F)) := by sorry
