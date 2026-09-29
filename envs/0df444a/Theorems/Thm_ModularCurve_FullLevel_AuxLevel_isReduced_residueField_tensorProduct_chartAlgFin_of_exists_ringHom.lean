-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_AuxLevel_isReduced_residueField_tensorProduct_chartAlgFin_of_exists_ringHom
-- name    : ModularCurve.FullLevel.AuxLevel.isReduced_residueField_tensorProduct_chartAlgFin_of_exists_ringHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:22.181174+00:00
-- url     : https://prove2.me/theorems/e927f2bc-257e-59a2-81db-fbcdb79f503f
-- title:
--   Reducedness of the special fibre of the j-finite chart
-- statement:
--   Let $q$ be a prime with $q\ge 5$, let $M'$ be a nonzero natural number with $q\nmid M'$, and let $\ell$ be a prime with $\ell\ge 3$, $\ell\ne q$ and $\ell\nmid M'$. Let $L$ be a field of characteristic $0$ containing a primitive $(q\ell)$-th root of unity $\xi$, and assume there is a ring homomorphism $\iota\colon L\to\mathbb{C}$ with $\iota(\xi)=\exp(2\pi i/(q\ell))$. Let $K$ be the intermediate field of the Laurent series field $L(\!(X)\!)$ over $L$ given by [`ModularCurve.laurentBaseChange`](def/ModularCurve_LaurentCoeff.html#L103), i.e. generated over $L$ by the coefficientwise image of the $q$-expansion function field [`ModularCurve.xHFunctionField`](def/ModularCurve_XH.html#L79) over $\mathbb{Q}$ of level $(q\ell)^2M'$ with subgroup $H=\ker\bigl((\mathbb{Z}/(q\ell)^2M')^\times\to(\mathbb{Z}/q\ell)^\times\bigr)$, the units congruent to $1$ modulo $q\ell$. Let $A$ be a discrete valuation domain with an $L$-algebra structure making $L$ its fraction field, with $q$ lying in the maximal ideal of $A$, and with an $A$-algebra structure on $K$ compatible with that on $L$. Let $j\in K$ be nonzero and have image in $L(\!(X)\!)$ the $q$-expansion $X^{-1}\cdot\mathrm{jNumQ}$ of the modular function $j$, pushed forward along $\mathbb{Q}\to L$. Then the ring $\kappa(A)\otimes_A C$ is reduced, where $\kappa(A)$ is the residue field of $A$ and $C=$ [`AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A K j`](def/AlgebraicCurve_TwoChartIntegralModel.html#L142) is the subalgebra of elements of $K$ integral over $A[j]$.
--
--   This is the reducedness of the special fibre of the $j$-finite chart of the two-chart integral model of the full-level $q$-expansion field, in the style of Katz–Mazur's theorem that the characteristic-$q$ fibre of the full level-$q$ moduli curve is a reduced curve whose Igusa components cross at the supersingular points. It is used in the construction of the Jacobian of the full-level modular curve, being cited by [`ModularCurve.FullLevel.AuxLevel.exists_chartAlgFin_tensorProduct_ringEquiv_of_cyclotomicConstants_of_isAlgClosed`](thm.html#ModularCurve.FullLevel.AuxLevel.exists_chartAlgFin_tensorProduct_ringEquiv_of_cyclotomicConstants_of_isAlgClosed).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_AuxLevel_isReduced_residueField_tensorProduct_chartAlgFin_of_exists_ringHom.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_JqCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem ModularCurve.FullLevel.AuxLevel.isReduced_residueField_tensorProduct_chartAlgFin_of_exists_ringHom
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))
    (hιξ : ∃ ι : L →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ)))
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M')
        (ModularCurve.FullLevel.levelH (q * ℓ) M')))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)] :
    IsReduced (TensorProduct A (IsLocalRing.ResidueField A)
      ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) := by sorry
