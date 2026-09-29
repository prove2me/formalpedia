-- Prove2me | Theorems.Thm_ModularCurve_XOneP_exists_postComp_eq_of_comp_fst_eq_comp_galoisTransport_of_classifies_fibre_twoChartModel_x1_mul
-- name    : ModularCurve.XOneP.exists_postComp_eq_of_comp_fst_eq_comp_galoisTransport_of_classifies_fibre_twoChartModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.601084+00:00
-- url     : https://prove2.me/theorems/61e95495-3fd2-5209-bbf1-d7bff3d2521f
-- title:
--   Galois transport of Pic⁰ on the special fibre
-- statement:
--   Fix a prime $p$ and $M \geq 5$ with $p \nmid M$, a characteristic-zero field $L$ that is a cyclotomic extension of $\mathbb{Q}$ for $\{p\}$, a primitive $p$-th root of unity $\zeta \in L$, and the intermediate field $K$ of $L \subseteq \mathrm{LaurentSeries}\,L$ obtained by adjoining to $L$ the coefficientwise image of the function field of $X_1(Mp)$; let $A$ be a discrete valuation domain with fraction field $L$ whose maximal ideal contains $p$ and whose image in $L$ contains $\zeta$, with $K$ an $A$-algebra compatibly, and let $j \in K$ be nonzero with Laurent expansion the $q$-expansion [`ModularCurve.jq`](def/ModularCurve_X0.html#L157). Let $k$ be an algebraically closed $A$-algebra of characteristic $p$. Write $X \to \operatorname{Spec} A$ for [`ModularCurve.TwoChart.modelTo A K j`](def/ModularCurve_TwoChartModel.html#L252), assumed proper, with a section $\varepsilon$. Let $D$ be a relative $\mathrm{Pic}^0$ datum for $X$ (a scheme $P$ over $\operatorname{Spec} A$ with a zero section), assumed to represent, for some choice of Poincaré bundle, the functor of rigidified line bundles that are fibrewise algebraically equivalent to zero, with $D \to \operatorname{Spec} A$ smooth and separated; assume further that the base change $D_k$ represents the corresponding functor for $X_k = X \times_A k$ with its base-changed section, via a representability datum `hreps` whose Poincaré bundle is isomorphic to the base change of the pullback of that of $D$. Let $\mathrm{Gal}(L/\mathbb{Q})$ act on $A$ by semiring automorphisms compatibly with $A \to L$, the induced action on $A$ becoming trivial after mapping to $k$. Fix $s \in \mathrm{Gal}(L/\mathbb{Q})$, an endomorphism $u$ of $X$ lying over $\operatorname{Spec}(s^{-1})$, an automorphism $u_k$ of $X_k$ over $\operatorname{Spec} k$ whose composite with the first projection is the first projection followed by $u$, a proof that $\operatorname{Spec}(s)$ followed by $\operatorname{Spec}(s^{-1})$ is the identity, and a morphism $N : P \to P$ with $N$ followed by $D \to \operatorname{Spec} A$ equal to $D \to \operatorname{Spec} A$ followed by $\operatorname{Spec}(s)$, such that for every $t : T \to \operatorname{Spec} A$ and every $a : T \to P$ over $t$, the pullback of the Poincaré bundle along $a$ followed by $N$ (taken over $t$ followed by $\operatorname{Spec}(s)$) is isomorphic to the rigidification, along `rigSection` and the second projection, of the $u$-induced pullback of the pullback of the Poincaré bundle along $a$. Then there is an endomorphism $\theta_k$ of $D_k$ over $\operatorname{Spec} k$ with two properties: first, for every $t : T \to \operatorname{Spec} k$, every pair $P_1, P_2$ of rigidified line bundles on $X_k \times_k T$ that are fibrewise algebraically equivalent to zero, and every invertible module $Q$ on $T$, if $P_2$ is isomorphic to the pullback of $P_1$ along the curve change induced by $u_k$ tensored with the pullback of $Q$, then the classifying morphism of $P_1$ followed by $\theta_k$ equals the classifying morphism of $P_2$; second, for all $k$-points $a, a'$ of $D_k$, if $a'$ followed by the first projection $P \times_A k \to P$ equals $a$ followed by that projection and then $N$, then $a' = a$ followed by $\theta_k$.
--
--   This is the compatibility of a semilinear Galois transport of the relative $\mathrm{Pic}^0$ of the two-chart model of $X_1(Mp)$ with passage to the special fibre: the transport $N$ over $\operatorname{Spec}(s)$ induces on $\mathrm{Pic}^0$ of the mod-$p$ curve the $k$-linear transport along the reduction $u_k$, on the level both of classifying maps of rigidified line bundles and of $k$-points. It feeds the descent argument for $J_1$ that identifies Galois action and Picard functoriality on points of the special fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_exists_postComp_eq_of_comp_fst_eq_comp_galoisTransport_of_classifies_fibre_twoChartModel_x1_mul.lean

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

theorem ModularCurve.XOneP.exists_postComp_eq_of_comp_fst_eq_comp_galoisTransport_of_classifies_fibre_twoChartModel_x1_mul
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

    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of A))) (ModularCurve.TwoChart.modelTo A (↥K) j))

    (D : RelativePic0Designation A (ModularCurve.TwoChart.modelTo A (↥K) j))
    (hrep : Nonempty (RepresentsRelSubPic (ModularCurve.TwoChart.modelTo A (↥K) j) ε (algEquivZeroCut (ModularCurve.TwoChart.modelTo A (↥K) j) ε) D))
    (hsm : Smooth D.toBase) (hsep : IsSeparated D.toBase)

    (hreps : RepresentsRelSubPic (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k) (sectionBaseChange k ε)
      (algEquivZeroCut (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k) (sectionBaseChange k ε)) (D.baseChange k))
    (hPk : Nonempty (hreps.poincare.L ≅ (BaseChange.ofR (ModularCurve.TwoChart.modelTo A (↥K) j) ε k
      (hrep.some.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap A k), pullback.condition⟩)).L))

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
    ∃ θk : SchemeHomOver (D.baseChange k).toBase (D.baseChange k).toBase,

      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k))
          (P₁ : RigidifiedLineBundle (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k) (sectionBaseChange k ε) t) (hP₁ : FibrewiseAlgEquivZero P₁)
          (P₂ : RigidifiedLineBundle (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k) (sectionBaseChange k ε) t) (hP₂ : FibrewiseAlgEquivZero P₂)
          (Q : T.Modules), Scheme.Modules.IsInvertible Q →
          Nonempty (P₂.L ≅ (Scheme.Modules.pullback (curveChange (c := (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k)) (c' := (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k)) uk.hom huk₂ t)).obj P₁.L ⊗
            (Scheme.Modules.pullback (pullback.snd (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k) t)).obj Q) →
          postComp θk (hreps.classify t P₁ hP₁) = hreps.classify t P₂ hP₂) ∧

      (∀ (a a' : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (D.baseChange k).toBase),
          a'.1 ≫ pullback.fst D.toBase (specMap A k) = (a.1 ≫ pullback.fst D.toBase (specMap A k)) ≫ N.1 →
          a' = postComp θk a) := by sorry
