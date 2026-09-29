-- Prove2me | Theorems.Thm_ModularCurve_XOneP_exists_injective_not_isRegularLocalRing_stalk_specialFibre_of_mem_ssJSet_twoChartIntegralModel_x1_mul
-- name    : ModularCurve.XOneP.exists_injective_not_isRegularLocalRing_stalk_specialFibre_of_mem_ssJSet_twoChartIntegralModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.601084+00:00
-- url     : https://prove2.me/theorems/a9f8374a-5811-50b3-948d-1a38a803fb26
-- title:
--   Non-regular points above supersingular j-invariants on X₁(Mp)
-- statement:
--   Fix a prime $p$ and $M \ge 5$ with $p \nmid M$, a field $L$ of characteristic zero that is a cyclotomic extension of $\mathbb{Q}$ of type $\{p\}$, and a primitive $p$-th root of unity $\zeta \in L$. Let $K$ be the $L$-subfield of $\mathrm{LaurentSeries}\,L$ obtained as `laurentBaseChange` of the $q$-expansion function field of $X_1(Mp)$ over $\mathbb{Q}$, i.e. generated over $L$ by the coefficientwise image of that field under `coeffEmb`. Let $A$ be a discrete valuation domain with fraction field $L$ such that $p$ lies in its maximal ideal and $\zeta$ is in the image of $A$, with an $A$-algebra structure on $K$ compatible with $L$, and let $j \in K$ be a nonzero element whose underlying Laurent series is the image under `coeffEmb` of the $q$-expansion $q^{-1}\cdot(\text{numerator series})$ of the modular invariant. Let $\Omega_0$ be an algebraically closed $A$-algebra field of characteristic $p$, and let $\bar{j}$ be the element of the $q$-expansion function field `x1FunctionFieldC` of $\Gamma_1(M)$ over $\Omega_0$ whose Laurent series is `jqModC`. Write $X =$ `TwoChartIntegralModel A K j` (the pushout of the finite and infinite charts) with structure morphism `toBase` to $\operatorname{Spec} A$, and let $\bar{X}_s$ be the pullback of `toBase` along $\operatorname{Spec}$ of $A \to \Omega_0$. Then there is an injective map $\iota$ from the set of places $v$ of the function field of $X_1(M)$ over $\Omega_0$ — that is, valuation subrings containing $\Omega_0$, proper, and principal ideal rings — such that $\bar{j}$ lies in the valuation subring of $v$ and the residue $v$-value `evalAt` $\bar{j}$ belongs to $\mathrm{ssJSet}\,p\,\Omega_0$, the set of $a$ such that every elliptic Weierstrass curve over $\Omega_0$ with $j$-invariant $a$ has no nonzero $p$-torsion affine point, into the underlying space of $\bar{X}_s$, with the following properties for every such $v$: the stalk of $\bar{X}_s$ at $\iota(v)$ is not a regular local ring, and there is a point $y$ of the finite chart $\operatorname{Spec}(\mathrm{chartAlgFin}\,A\,K\,j)$, where $\mathrm{chartAlgFin}$ consists of the elements of $K$ integral over $A[j]$, whose image under the base map of `ιFin` equals the image of $\iota(v)$ under the first pullback projection, and such that for every algebraically closed field $\Omega$ of characteristic $p$ and every ring homomorphism $\varphi$ from $\mathrm{chartAlgFin}\,A\,K\,j$ to $\Omega$ with kernel the prime of $y$, the value $\varphi(j)$ lies in $\mathrm{ssJSet}\,p\,\Omega$.
--
--   This records the classical fact that the special fibre of the integral model of $X_1(Mp)$ at $p$ acquires singularities exactly above the supersingular points of $X_1(M)$ in characteristic $p$, in the form needed downstream: each supersingular place of the level-$M$ function field gives, injectively, a non-regular point of the geometric special fibre of the two-chart model at level $Mp$, together with a witness in the $j$-finite chart whose $j$-value remains supersingular under any residue map. It is used in the genus and non-smoothness estimates for the level-$Mp$ model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_exists_injective_not_isRegularLocalRing_stalk_specialFibre_of_mem_ssJSet_twoChartIntegralModel_x1_mul.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_AlgebraicCurve_PlaceEvaluation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem ModularCurve.XOneP.exists_injective_not_isRegularLocalRing_stalk_specialFibre_of_mem_ssJSet_twoChartIntegralModel_x1_mul
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (Ω₀ : Type) [Field Ω₀] [CharP Ω₀ p] [IsAlgClosed Ω₀] [DecidableEq Ω₀] [Algebra A Ω₀]
    (jbar : ↥(ModularCurve.x1FunctionFieldC Ω₀ M)) (hjbar : (jbar : LaurentSeries Ω₀) = ModularCurve.jqModC Ω₀) :
    ∃ ι : {v : AlgebraicCurve.Place Ω₀ ↥(ModularCurve.x1FunctionFieldC Ω₀ M) //
            (jbar : ↥(ModularCurve.x1FunctionFieldC Ω₀ M)) ∈ v.toValuationSubring ∧
              v.evalAt jbar ∈ ModularCurve.ssJSet p Ω₀} →
          ↥(pullback (AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j)
            (Spec.map (CommRingCat.ofHom (algebraMap A Ω₀)))),
      Function.Injective ι ∧
      ∀ v, ¬ IsRegularLocalRing
          ((pullback (AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j)
            (Spec.map (CommRingCat.ofHom (algebraMap A Ω₀)))).presheaf.stalk (ι v)) ∧
        ∃ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin A (↥K) j),
          (AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y =
            (pullback.fst (AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j)
              (Spec.map (CommRingCat.ofHom (algebraMap A Ω₀)))).base (ι v) ∧
          ∀ (Ω : Type) [Field Ω] [CharP Ω p] [IsAlgClosed Ω] [DecidableEq Ω]
            (φ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* Ω),
            RingHom.ker φ = y.asIdeal →
              φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K) j) ∈ ModularCurve.ssJSet p Ω := by sorry
