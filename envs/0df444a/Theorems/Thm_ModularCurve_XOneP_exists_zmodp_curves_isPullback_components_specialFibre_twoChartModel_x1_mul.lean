-- Prove2me | Theorems.Thm_ModularCurve_XOneP_exists_zmodp_curves_isPullback_components_specialFibre_twoChartModel_x1_mul
-- name    : ModularCurve.XOneP.exists_zmodp_curves_isPullback_components_specialFibre_twoChartModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:48.546916+00:00
-- url     : https://prove2.me/theorems/c34be6cd-9449-561d-a800-d75e945a25f8
-- title:
--   Components of the special fibre of X₁(Mp) descend to 𝔽ₚ
-- statement:
--   Let $p$ be a prime and $M$ a positive natural number with $5 \le M$ and $p \nmid M$; let $L$ be a field of characteristic zero which is a cyclotomic extension of $\mathbb{Q}$ for $\{p\}$, and $\zeta \in L$ a primitive $p$-th root of unity. Let $K$ be the intermediate field of $L \subseteq \mathrm{LaurentSeries}\,L$ obtained by adjoining to $L$ the image, under the coefficientwise map $\mathrm{coeffEmb}\,L$ induced by $\mathbb{Q} \to L$, of the field [`ModularCurve.x1FunctionField (M * p)`](def/ModularCurve_X1.html#L137) of $q$-expansions attached to $\Gamma_1(Mp)$. Let $A$ be a discrete valuation domain with fraction field $L$, such that $p$ lies in its maximal ideal and $\zeta$ is in the image of $A$, with compatible $A$-algebra structure on $K$, and let $j \in K$ be the element whose Laurent series is the image of [`ModularCurve.jq`](def/ModularCurve_X0.html#L157), with $j \ne 0$. Write $X \to \operatorname{Spec} A$ for [`ModularCurve.TwoChart.modelTo A K j`](def/ModularCurve_TwoChartModel.html#L252), the morphism from the pushout glueing the spectra of the subalgebras `chartAlg A K {j}` and `chartAlg A K {j⁻¹}` of $K$. Let $k$ be an algebraically closed field of characteristic $p$ which is an $A$-algebra, and let $c_1 : C_1 \to \operatorname{Spec} k$, $c_2 : C_2 \to \operatorname{Spec} k$ be proper, smooth of relative dimension $1$ and geometrically integral, together with closed immersions $i_1, i_2$ of $C_1, C_2$ into $X \times_A k$ commuting with the structure morphisms to $\operatorname{Spec} k$, such that every point of $X \times_A k$ lies in the range of $i_1$ or of $i_2$, and such that the scheme-theoretic intersection $C_1 \times_{X \times_A k} C_2$ is reduced with finite cardinality $n > 0$. Assume finally compatible algebra structures $A \to \mathbb{Z}/p \to k$. Then the kernel of $A \to \mathbb{Z}/p$ is the maximal ideal of $A$, and there exist schemes $C_{1,p}, C_{2,p}$ with morphisms $c_{1,p}, c_{2,p}$ to $\operatorname{Spec}(\mathbb{Z}/p)$ that are proper, smooth of relative dimension $1$ and geometrically integral, sections of $c_{1,p}$ and $c_{2,p}$ over $\operatorname{Spec}(\mathbb{Z}/p)$ (so each $C_{i,p}$ has a $\mathbb{Z}/p$-point), closed immersions $i_{1,p}, i_{2,p}$ of $C_{1,p}, C_{2,p}$ into $X \times_A \mathbb{Z}/p$ whose composites with the projection to $\operatorname{Spec}(\mathbb{Z}/p)$ are $c_{1,p}, c_{2,p}$, and morphisms $g_i : C_i \to C_{i,p}$ making $C_i$ the pullback of $c_{i,p}$ along $\operatorname{Spec} k \to \operatorname{Spec}(\mathbb{Z}/p)$, such that $g_i$ followed by $i_{i,p}$ followed by the projection to $X$ equals $i_i$ followed by the projection to $X$.
--
--   This is the descent to the prime field of the two irreducible components of the geometric special fibre of the two-chart model of $X_1(Mp)$ at $p$, together with their embeddings into the model and with $\mathbb{F}_p$-rational points on each component. It is used in the subsequent analysis of the relative $\mathrm{Pic}^0$ of the special fibre of this model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_exists_zmodp_curves_isPullback_components_specialFibre_twoChartModel_x1_mul.lean

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JOnePGeom
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_JacJ1Iface
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.SmoothProperCurve

theorem ModularCurve.XOneP.exists_zmodp_curves_isPullback_components_specialFibre_twoChartModel_x1_mul
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]

    (k : Type) [Field k] [IsAlgClosed k] [CharP k p] [Algebra A k]
    (C₁ C₂ : Scheme.{0}) (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁] [GeometricallyIntegral c₁]
    [IsProper c₂] [SmoothOfRelativeDimension 1 c₂] [GeometricallyIntegral c₂]
    (i₁ : SchemeHomOver c₁ (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k)) (i₂ : SchemeHomOver c₂ (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k))
    [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hcover : ∀ z : ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)), z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)
    (hred : IsReduced (pullback i₁.1 i₂.1)) (n : ℕ) (hn : Nat.card ↥(pullback i₁.1 i₂.1) = n) (hn0 : 0 < n)
    [Algebra A (ZMod p)] [Algebra (ZMod p) k] [IsScalarTower A (ZMod p) k] :
    ∃ (C₁ₚ C₂ₚ : Scheme.{0}) (c₁ₚ : C₁ₚ ⟶ Spec (CommRingCat.of (ZMod p))) (c₂ₚ : C₂ₚ ⟶ Spec (CommRingCat.of (ZMod p)))
      (i₁ₚ : C₁ₚ ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (ZMod p)))
      (i₂ₚ : C₂ₚ ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (ZMod p)))
      (g₁ : C₁ ⟶ C₁ₚ) (g₂ : C₂ ⟶ C₂ₚ)
      (ε₁ₚ : SchemeHomOver (𝟙 (Spec (CommRingCat.of (ZMod p)))) c₁ₚ) (ε₂ₚ : SchemeHomOver (𝟙 (Spec (CommRingCat.of (ZMod p)))) c₂ₚ),
      RingHom.ker (algebraMap A (ZMod p)) = IsLocalRing.maximalIdeal A ∧
      (IsProper c₁ₚ ∧ SmoothOfRelativeDimension 1 c₁ₚ ∧ GeometricallyIntegral c₁ₚ) ∧
      (IsProper c₂ₚ ∧ SmoothOfRelativeDimension 1 c₂ₚ ∧ GeometricallyIntegral c₂ₚ) ∧
      IsPullback g₁ c₁ c₁ₚ (specMap (ZMod p) k) ∧ IsPullback g₂ c₂ c₂ₚ (specMap (ZMod p) k) ∧
      IsClosedImmersion i₁ₚ ∧ IsClosedImmersion i₂ₚ ∧
      i₁ₚ ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (ZMod p)) = c₁ₚ ∧
      i₂ₚ ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (ZMod p)) = c₂ₚ ∧
      g₁ ≫ i₁ₚ ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (ZMod p)) = i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) ∧
      g₂ ≫ i₂ₚ ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (ZMod p)) = i₂.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) := by sorry
