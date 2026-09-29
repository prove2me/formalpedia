-- Prove2me | Theorems.Thm_ModularCurve_XOneP_comap_ne_of_mem_minimalPrimes_map_maximalIdeal_chartAlgFin_twoChartModel_x1_mul
-- name    : ModularCurve.XOneP.comap_ne_of_mem_minimalPrimes_map_maximalIdeal_chartAlgFin_twoChartModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.601084+00:00
-- url     : https://prove2.me/theorems/01232f64-0d92-54b1-a0a9-cf8efd200ada
-- title:
--   No minimal prime of the special fibre is fixed
-- statement:
--   Let $p$ be a prime and $M\ge 5$ an integer not divisible by $p$; let $L$ be a field of characteristic zero that is a cyclotomic extension of $\mathbb{Q}$ of type $\{p\}$, with $\zeta\in L$ a primitive $p$-th root of unity. Let $K$ be the $L$-subfield of $L((q))$ obtained by adjoining to $L$ the coefficientwise image of the $q$-expansion function field of $\Gamma_1(Mp)$ over $\mathbb{Q}$, and let $A$ be a discrete valuation domain with fraction field $L$ such that $p$ lies in $\mathfrak m_A$ and $\zeta$ lies in the image of $A$, acting on $K$ through the tower $A\to L\to K$. Let $j\in K$ be nonzero with image in $L((q))$ the coefficientwise image of $q^{-1}\cdot jNumQ$, i.e. the $q$-expansion of the modular invariant. Write $\mathcal O$ for the subalgebra of elements of $K$ integral over $A[j]$ (the `chartAlgFin` construction, given identically in both namespaces used). Assume $\sigma_K$ is an $L$-algebra automorphism of $K$ with $b\in\mathcal O\iff\sigma_K b\in\mathcal O$, and such that any valuation subring $W_0$ of $K$ consisting exactly of the quotients $x/y$ with $x,y\in A[[q]]$ and $y$ nonzero modulo $\mathfrak m_A$ satisfies $\sigma_K^{-1}(W_0)\ne W_0$. Let $\sigma_{\mathrm{Fin}}$ be an $A$-algebra endomorphism of $\mathcal O$ whose underlying map on $K$ is $\sigma_K$. Then for every minimal prime $\mathfrak P$ of $\mathfrak m_A\mathcal O$ one has $\sigma_{\mathrm{Fin}}^{-1}(\mathfrak P)\ne\mathfrak P$.
--
--   This is the assertion that an $L$-automorphism of the function field of $X_1(Mp)$ which preserves the $j$-finite integral chart but moves the Gauss valuation ring permutes the irreducible components of the special fibre of that chart without fixing any of them; concretely, the special fibre has exactly two such components and the automorphism interchanges them. It feeds the component-group analysis of the model of $X_1(Mp)$ over the local ring at $p$ of $\mathbb{Q}(\zeta_p)$, being used in [`ModularCurve.XOneP.image_ne_of_mem_irreducibleComponents_pullback_of_not_smooth_twoChartModel_x1_mul`](thm.html#ModularCurve.XOneP.image_ne_of_mem_irreducibleComponents_pullback_of_not_smooth_twoChartModel_x1_mul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_comap_ne_of_mem_minimalPrimes_map_maximalIdeal_chartAlgFin_twoChartModel_x1_mul.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_JacJ1Iface
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_RelPicardPullback

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard
  AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian TensorProduct

theorem ModularCurve.XOneP.comap_ne_of_mem_minimalPrimes_map_maximalIdeal_chartAlgFin_twoChartModel_x1_mul
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (σK : ↥K ≃ₐ[L] ↥K)
    (hσK₂ : ∀ b : ↥K, b ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j ↔
      σK b ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
    (hσK₃ : ∀ W₀ : ValuationSubring ↥K,
        (∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
          (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
            = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L))) →
        W₀.comap (σK : ↥K ≃ₐ[L] ↥K).toAlgHom.toRingHom ≠ W₀)
    (σFin : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) →ₐ[A] ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))
    (hσFin : ∀ x, ((σFin x : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) : ↥K) = σK x)
    :
    ∀ 𝔓 ∈ (Ideal.map (algebraMap A ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) (IsLocalRing.maximalIdeal A)).minimalPrimes,
      Ideal.comap σFin.toRingHom 𝔓 ≠ 𝔓 := by sorry
