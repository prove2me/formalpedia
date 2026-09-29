-- Prove2me | Theorems.Thm_ModularCurve_XOneP_exists_rigidifiedLineBundle_fibrewiseAlgEquivZero_and_pullbackAlong_iso_tensorPow_poincare_of_map_maximalIdeal_eq_twoChartModel_x1_mul
-- name    : ModularCurve.XOneP.exists_rigidifiedLineBundle_fibrewiseAlgEquivZero_and_pullbackAlong_iso_tensorPow_poincare_of_map_maximalIdeal_eq_twoChartModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.601084+00:00
-- url     : https://prove2.me/theorems/642cc567-ba67-5f39-9f06-f0bc85c694b7
-- title:
--   Extending the n-th power of a Pic⁰ point over O
-- statement:
--   Fix a prime $p$ and $M\ge 5$ with $p\nmid M$, a field $L$ of characteristic zero that is a $\{p\}$-cyclotomic extension of $\mathbb{Q}$ with a primitive $p$-th root of unity $\zeta$, and the intermediate field $K$ of $L\subseteq \mathrm{LaurentSeries}\,L$ obtained by adjoining to $L$ the coefficientwise image of the function field `x1FunctionField (M * p)`. Let $A$ be a discrete valuation domain with fraction field $L$ such that $p$ lies in its maximal ideal and $\zeta$ comes from $A$, let $K$ be an $A$-algebra compatibly with $L$, and let $j\in K$ be nonzero with Laurent expansion the $q$-expansion [`ModularCurve.jq`](def/ModularCurve_X0.html#L157); write $X\to\operatorname{Spec}A$ for the two-chart model [`ModularCurve.TwoChart.modelTo A K j`](def/ModularCurve_TwoChartModel.html#L252), assumed proper. Let $k$ be an algebraically closed $A$-field of characteristic $p$, and let $c_1\colon C_1\to\operatorname{Spec}k$, $c_2\colon C_2\to\operatorname{Spec}k$ be proper, smooth of relative dimension $1$ and geometrically integral, with closed immersions $i_1,i_2$ over $\operatorname{Spec}k$ into $X_k=X\times_A k$ whose images together cover $X_k$; assume $C_1\times_{X_k}C_2$ is reduced with exactly $n>0$ points. Let $\varepsilon$ be a section of $X\to\operatorname{Spec}A$, and $D$ a datum consisting of a scheme with a structure morphism $D.\mathrm{toBase}$ to $\operatorname{Spec}A$ and a zero section of it, together with the (nonempty) data `RepresentsRelSubPic` that $D.\mathrm{toBase}$ carries a Poincaré $\varepsilon$-rigidified line bundle, fibrewise algebraically equivalent to zero, which universally represents the $\varepsilon$-rigidified line bundles with that fibrewise property, and whose pullback along the zero section is the unit. Let $O$ be a discrete valuation domain with a ring map $\rho_O\colon A\to O$ carrying the maximal ideal of $A$ onto that of $O$, a surjection $\mathrm{to}\kappa\colon O\to k$ over $A$, a morphism $bc\colon X_k\to X_O$ compatible with the projection to $X$ and with $\operatorname{Spec}(\mathrm{to}\kappa)$ on the base, and fraction field $T'$. Then for every $T'$-point $y$ of $D.\mathrm{toBase}$ over $\operatorname{Spec}A$ there exists an $\varepsilon$-rigidified line bundle $\mathcal{M}$ on $X_O=X\times_A\operatorname{Spec}O$ which is fibrewise algebraically equivalent to zero — for every algebraically closed field and every point of $\operatorname{Spec}O$ with values in it, the restriction of $\mathcal{M}$ to that geometric fibre satisfies `IsAlgEquivZero` — such that the module of the pullback of $\mathcal{M}$ along $\operatorname{Spec}T'\to\operatorname{Spec}O$ is isomorphic to the $n$-th tensor power (iterated $\otimes$ starting from the unit) of the module of the pullback of the Poincaré bundle along $y$.
--
--   This is the line-bundle extension step in the determination of the component group of the Jacobian of $X_1(Mp)$ at $p$: over an unramified discrete valuation ring whose closed fibre is the union of two Igusa curves meeting in $n$ points, $n$ times any point of $\mathrm{Pic}^0$ over the fraction field extends to a fibrewise algebraically trivial bundle on the whole model. It is used in the deduction that the relevant points of $\mathrm{Pic}^0$ become divisible by $n$ over the valuation subring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_exists_rigidifiedLineBundle_fibrewiseAlgEquivZero_and_pullbackAlong_iso_tensorPow_poincare_of_map_maximalIdeal_eq_twoChartModel_x1_mul.lean

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_ModulesTensorPow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.SmoothProperCurve

theorem ModularCurve.XOneP.exists_rigidifiedLineBundle_fibrewiseAlgEquivZero_and_pullbackAlong_iso_tensorPow_poincare_of_map_maximalIdeal_eq_twoChartModel_x1_mul
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

    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of A))) (ModularCurve.TwoChart.modelTo A (↥K) j))
    (D : RelativePic0Designation A (ModularCurve.TwoChart.modelTo A (↥K) j))
    (hrep : Nonempty (RepresentsRelSubPic (ModularCurve.TwoChart.modelTo A (↥K) j) ε (algEquivZeroCut (ModularCurve.TwoChart.modelTo A (↥K) j) ε) D))

    [IsProper (ModularCurve.TwoChart.modelTo A (↥K) j)]

    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (ρO : A →+* O) (hunr : Ideal.map ρO (IsLocalRing.maximalIdeal A) = IsLocalRing.maximalIdeal O)
    (toκ : O →+* k) (htoκ : toκ.comp ρO = algebraMap A k)
    (bc : pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ρO)))
    (hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _)
    (hbc₂ : bc ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom toκ))

    (htoκs : Function.Surjective toκ)
    (T' : Type) [Field T'] [Algebra O T'] [IsFractionRing O T']

    (y : SchemeHomOver (Spec.map (CommRingCat.ofHom ((algebraMap O T').comp ρO))) D.toBase) :
    ∃ M : RigidifiedLineBundle (ModularCurve.TwoChart.modelTo A (↥K) j) ε (Spec.map (CommRingCat.ofHom ρO)),
      FibrewiseAlgEquivZero M ∧
      Nonempty ((M.pullbackAlong ⟨Spec.map (CommRingCat.ofHom (algebraMap O T')),
          by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]⟩).L ≅
        (hrep.some.poincare.pullbackAlong y).L.tensorPow n) := by sorry
