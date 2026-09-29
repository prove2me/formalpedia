-- Prove2me | Theorems.Thm_ModularCurve_XOneP_image_ne_of_mem_irreducibleComponents_pullback_of_not_smooth_twoChartModel_x1_mul
-- name    : ModularCurve.XOneP.image_ne_of_mem_irreducibleComponents_pullback_of_not_smooth_twoChartModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:48.546916+00:00
-- url     : https://prove2.me/theorems/7932d291-939b-50ee-b521-246fa4431abc
-- title:
--   No component of a bad geometric fibre is fixed
-- statement:
--   Fix a prime $p$ and an integer $M\ge 5$ with $p\nmid M$, a field $L$ of characteristic zero that is a cyclotomic extension of $\mathbb{Q}$ of order $p$, and a primitive $p$-th root of unity $\zeta\in L$. Let $K$ be an intermediate field of $L((q))=$ `LaurentSeries L` over $L$, assumed equal to [`ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))`](def/ModularCurve_LaurentCoeff.html#L103), the subfield generated over $L$ by the coefficientwise image under $\mathbb{Q}\to L$ of the function field attached to $X_1(Mp)$. Let $A$ be a discrete valuation domain with fraction field $L$ whose maximal ideal contains $p$ and whose image in $L$ contains $\zeta$, with $K$ an $A$-algebra compatibly with $A\to L\to K$. Let $j\in K$, nonzero, whose image in $L((q))$ is the $q$-expansion [`ModularCurve.jq`](def/ModularCurve_X0.html#L157) $=q^{-1}\cdot(\text{power series } jNumQ)$ with coefficients pushed into $L$. Let $\sigma_K$ be an $L$-algebra automorphism of $K$ such that (i) for $b\in K$, $b$ is integral over $A[j]$ if and only if $\sigma_K b$ is, and (ii) any valuation subring $W_0$ of $K$ consisting exactly of the quotients $x/y$ with $x,y$ power series over $A$ and $y$ having nonzero reduction modulo the maximal ideal of $A$ (the Gauss subring) satisfies $\sigma_K^{-1}$-comap $W_0\ne W_0$. Let $\sigma$ be an automorphism of the scheme [`ModularCurve.TwoChartModel A K j`](def/ModularCurve_TwoChartModel.html#L229) — the pushout of the two maps from the spectrum of the elements integral over $A[j,j^{-1}]$ to the spectra of the elements integral over $A[j]$ and over $A[j^{-1}]$ — commuting with the structure morphism `modelTo` to $\operatorname{Spec} A$, and let $\sigma_{\mathrm{Fin}}$ be an $A$-algebra endomorphism of the $j$-finite chart algebra inducing $\sigma_K$ on elements of $K$ and inducing $\sigma$ on the $j$-finite chart, in the sense that $\operatorname{Spec}\sigma_{\mathrm{Fin}}$ followed by `ιFin` equals `ιFin` followed by $\sigma$. Then for every algebraically closed field $k$ and every morphism $x\colon\operatorname{Spec} k\to\operatorname{Spec} A$ for which the projection from the fibre product of `modelTo` and $x$ to $\operatorname{Spec} k$ is not smooth, and for every irreducible component $Z$ of the underlying space of that fibre product, the image of $Z$ under the base change of $\sigma$ (the map induced on the pullback by $\sigma$ and the identities) is different from $Z$.
--
--   The statement says that on a geometric fibre of bad reduction of the two-chart integral model of $X_1(Mp)$ over a discrete valuation ring with residue characteristic $p$, the automorphism induced by a field automorphism of the function field moving the Gauss valuation permutes the irreducible components without fixed points. It feeds the construction of the swap of connected components used in the analysis of the component groups of the Jacobian at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_image_ne_of_mem_irreducibleComponents_pullback_of_not_smooth_twoChartModel_x1_mul.lean

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

theorem ModularCurve.XOneP.image_ne_of_mem_irreducibleComponents_pullback_of_not_smooth_twoChartModel_x1_mul
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
    (σ : ModularCurve.TwoChartModel A (↥K) j ≅ ModularCurve.TwoChartModel A (↥K) j) (hσ : σ.hom ≫ ModularCurve.TwoChart.modelTo A (↥K) j = ModularCurve.TwoChart.modelTo A (↥K) j)
    (σFin : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) →ₐ[A] ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))
    (hσFin : ∀ x, ((σFin x : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) : ↥K) = σK x)
    (hσι : Spec.map (CommRingCat.ofHom σFin.toRingHom) ≫ ModularCurve.TwoChart.ιFin A (↥K) j = ModularCurve.TwoChart.ιFin A (↥K) j ≫ σ.hom)
    :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of A)),
      ¬ Smooth (pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) x) →
      ∀ Z ∈ irreducibleComponents ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) x),
        (pullback.map (ModularCurve.TwoChart.modelTo A (↥K) j) x (ModularCurve.TwoChart.modelTo A (↥K) j) x σ.hom (𝟙 _) (𝟙 _)
            (by rw [Category.comp_id, hσ]) (by rw [Category.comp_id, Category.id_comp])).base '' Z ≠ Z := by sorry
