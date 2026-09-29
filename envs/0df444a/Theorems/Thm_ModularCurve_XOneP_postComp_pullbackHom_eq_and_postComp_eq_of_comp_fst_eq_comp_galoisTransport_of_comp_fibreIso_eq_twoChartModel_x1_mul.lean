-- Prove2me | Theorems.Thm_ModularCurve_XOneP_postComp_pullbackHom_eq_and_postComp_eq_of_comp_fst_eq_comp_galoisTransport_of_comp_fibreIso_eq_twoChartModel_x1_mul
-- name    : ModularCurve.XOneP.postComp_pullbackHom_eq_and_postComp_eq_of_comp_fst_eq_comp_galoisTransport_of_comp_fibreIso_eq_twoChartModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:48.546916+00:00
-- url     : https://prove2.me/theorems/314319b7-b4f1-56fb-a99d-dfabd1211116
-- title:
--   Galois transport fixes Pic⁰ of pointwise-fixed components
-- statement:
--   Fix a prime $p$ and $M$ with $5 \le M$ and $p \nmid M$; let $L$ be a field of characteristic zero that is a cyclotomic extension of $\mathbb{Q}$ for $\{p\}$, $\zeta \in L$ a primitive $p$-th root of unity, and $K$ the intermediate field of $L \subseteq \mathrm{LaurentSeries}\,L$ equal to [`ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))`](def/ModularCurve_LaurentCoeff.html#L103). Let $A$ be a discrete valuation domain with fraction field $L$ such that $p$ lies in its maximal ideal and $\zeta$ comes from $A$, with $K$ an $A$-algebra compatibly, and let $j \in K$, $j \ne 0$, have image the coefficientwise embedding of the $q$-expansion [`ModularCurve.jq`](def/ModularCurve_X0.html#L157); write $X \to \operatorname{Spec} A$ for [`ModularCurve.TwoChart.modelTo A K j`](def/ModularCurve_TwoChartModel.html#L252), assumed proper. Let $k$ be an algebraically closed $A$-algebra field of characteristic $p$, and $c_1, c_2$ proper, geometrically integral, smooth of relative dimension $1$ structure morphisms of $C_1, C_2$ over $k$, together with closed immersions $i_1, i_2$ of $C_1, C_2$ over $k$ into the fibre $X_k = X \times_{\operatorname{Spec} A} \operatorname{Spec} k$, whose images cover $X_k$, with $C_1 \times_{X_k} C_2$ reduced of cardinality $n > 0$. Further data: a section $\varepsilon$ of $X \to \operatorname{Spec} A$, sections $\varepsilon_1, \varepsilon_2$ of $c_1, c_2$ with $\varepsilon_1$ followed by $i_1$ equal to the base change of $\varepsilon$; a relative $\mathrm{Pic}^0$ designation $D$ for $X$ (a scheme with structure morphism to $\operatorname{Spec} A$ and a zero section) representing the condition of fibrewise algebraically trivial rigidified line bundles, with `D.toBase` smooth and separated; designations $D_1, D_2$ representing the corresponding conditions for $c_1, c_2$; a chosen representability datum `hreps` for the base change of $D$ to $k$, an isomorphism of its Poincaré bundle with the transfer to $k$ of the pullback of the Poincaré bundle of $D$ along $\mathrm{pr}_1 \colon D \times_{\operatorname{Spec} A} \operatorname{Spec} k \to D$; and a morphism $\nu_2$ from the base change of $D$ to $D_2$ over $k$ which, on every $k$-scheme point, classifies restriction of the Poincaré bundle along $i_2$ (rigidified by `rigidify` at $\varepsilon_2$). Finally, let $\mathrm{Gal}(L/\mathbb{Q})$ act on $A$ by semiring automorphisms compatibly with $A \to L$ and trivially on $A \to k$, let $s$ be such an automorphism, $u \colon X \to X$ a morphism covering $\operatorname{Spec}$ of $s^{-1}$ on $A$, $u_k$ an automorphism of $X_k$ compatible with $u$ through $\mathrm{pr}_1$ and over $\operatorname{Spec} k$, with $\operatorname{Spec}(s)$ followed by $\operatorname{Spec}(s^{-1})$ the identity, and let $N \colon D \to D$ cover $\operatorname{Spec}(s)$ and act on every point of $D$ as pullback of the Poincaré bundle along $u$ (rigidified at $\varepsilon$). The conclusion: for all $k$-points $a, a'$ of the base change of $D$ with $a'$ followed by $\mathrm{pr}_1$ equal to $a$ followed by $\mathrm{pr}_1$ then by $N$, one has (i) if $i_1$ followed by $u_k$ equals $i_1$, then $a'$ and $a$ have equal composites with the morphism to $D_1$ classifying restriction along $i_1$, and (ii) if $i_2$ followed by $u_k$ equals $i_2$, then $a'$ and $a$ have equal composites with $\nu_2$.
--
--   This is the transport statement for the Galois action on the relative $\mathrm{Pic}^0$ of the two-chart model of $X_1(Mp)$ over a ring of $p$-adic cyclotomic integers: a Galois element whose action on the special fibre fixes one of the two components pointwise does not move the projection of a point of $\mathrm{Pic}^0$ to the Jacobian of that component. It feeds the descent of the Galois action on the special fibre of $J_1(Mp)$, being used in the companion statement combining the Galois transport with the diamond operators and the Abel–Jacobi map.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_postComp_pullbackHom_eq_and_postComp_eq_of_comp_fst_eq_comp_galoisTransport_of_comp_fibreIso_eq_twoChartModel_x1_mul.lean

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
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_ModularCurve_JOnePOpsV2
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_AlgebraicCurve_CurveModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.SmoothProperCurve AlgebraicCurve

theorem ModularCurve.XOneP.postComp_pullbackHom_eq_and_postComp_eq_of_comp_fst_eq_comp_galoisTransport_of_comp_fibreIso_eq_twoChartModel_x1_mul
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
    (ε₁ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁) (ε₂ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₂)
    (hε₁ : ε₁.1 ≫ i₁.1 = (sectionBaseChange k ε).1)

    (D : RelativePic0Designation A (ModularCurve.TwoChart.modelTo A (↥K) j))
    (hrep : Nonempty (RepresentsRelSubPic (ModularCurve.TwoChart.modelTo A (↥K) j) ε (algEquivZeroCut (ModularCurve.TwoChart.modelTo A (↥K) j) ε) D))
    (hsm : Smooth D.toBase) (hsep : IsSeparated D.toBase)

    (hreps : RepresentsRelSubPic (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k) (sectionBaseChange k ε)
      (algEquivZeroCut (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k) (sectionBaseChange k ε)) (D.baseChange k))
    (hPk : Nonempty (hreps.poincare.L ≅ (BaseChange.ofR (ModularCurve.TwoChart.modelTo A (↥K) j) ε k
      (hrep.some.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap A k), pullback.condition⟩)).L))
    (D₁ : RelativePic0Designation k c₁) (hrep₁ : Nonempty (RepresentsRelSubPic c₁ ε₁ (algEquivZeroCut c₁ ε₁) D₁))
    (D₂ : RelativePic0Designation k c₂) (hrep₂ : Nonempty (RepresentsRelSubPic c₂ ε₂ (algEquivZeroCut c₂ ε₂) D₂))

    (ν₂ : SchemeHomOver (D.baseChange k).toBase D₂.toBase)
    (hν₂ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (a : SchemeHomOver t (D.baseChange k).toBase),
        Nonempty ((hrep₂.some.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a ν₂)).L ≅
          Scheme.Modules.rigidify (rigSection c₂ t ε₂) (pullback.snd c₂ t)
            ((Scheme.Modules.pullback (curveChange i₂.1 i₂.2 t)).obj (hreps.poincare.pullbackAlong a).L)))

    [IsProper (ModularCurve.TwoChart.modelTo A (↥K) j)]

    [MulSemiringAction (L ≃ₐ[ℚ] L) A]
    (hΓA : ∀ (s : L ≃ₐ[ℚ] L) (a : A), algebraMap A L (s • a) = s (algebraMap A L a))

    (hsk : ∀ (s' : L ≃ₐ[ℚ] L) (a : A), algebraMap A k (s' • a) = algebraMap A k a)
    (s : L ≃ₐ[ℚ] L)
    (u : ModularCurve.TwoChartModel A (↥K) j ⟶ ModularCurve.TwoChartModel A (↥K) j)
    (hu : u ≫ (ModularCurve.TwoChart.modelTo A (↥K) j) = (ModularCurve.TwoChart.modelTo A (↥K) j) ≫ (Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s⁻¹))))
    (uk : pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) ≅ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k))
    (huk₁ : uk.hom ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) =
      pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) ≫ u)
    (huk₂ : uk.hom ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) =
      pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k))

    (hsinv : (Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s))) ≫ (Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s⁻¹))) = 𝟙 (Spec (CommRingCat.of A)))

    (N : SchemeHomOver (D.toBase ≫ (Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s)))) D.toBase)
    (hN : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of A)) (a : SchemeHomOver t D.toBase),
      Nonempty ((hrep.some.poincare.pullbackAlong
          (⟨a.1 ≫ N.1, by rw [Category.assoc, N.2, ← Category.assoc, a.2]⟩ : SchemeHomOver (t ≫ (Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s)))) D.toBase)).L ≅
        Scheme.Modules.rigidify (rigSection (ModularCurve.TwoChart.modelTo A (↥K) j) (t ≫ (Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s)))) ε) (pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (t ≫ (Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s)))))
          ((Scheme.Modules.pullback
              (pullback.map (ModularCurve.TwoChart.modelTo A (↥K) j) (t ≫ (Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s)))) (ModularCurve.TwoChart.modelTo A (↥K) j) t u (𝟙 T) (Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s⁻¹)))
                hu.symm (by rw [Category.assoc, hsinv, Category.comp_id, Category.id_comp]))).obj
            (hrep.some.poincare.pullbackAlong a).L)))
    :
    ∀ (a a' : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (D.baseChange k).toBase),
      a'.1 ≫ pullback.fst D.toBase (specMap A k) = (a.1 ≫ pullback.fst D.toBase (specMap A k)) ≫ N.1 →
      (i₁.1 ≫ uk.hom = i₁.1 →
        postComp (RepresentsRelSubPic.pullbackHom i₁.1 i₁.2 hε₁ hreps hrep₁.some) a' =
          postComp (RepresentsRelSubPic.pullbackHom i₁.1 i₁.2 hε₁ hreps hrep₁.some) a) ∧
      (i₂.1 ≫ uk.hom = i₂.1 → postComp ν₂ a' = postComp ν₂ a) := by sorry
