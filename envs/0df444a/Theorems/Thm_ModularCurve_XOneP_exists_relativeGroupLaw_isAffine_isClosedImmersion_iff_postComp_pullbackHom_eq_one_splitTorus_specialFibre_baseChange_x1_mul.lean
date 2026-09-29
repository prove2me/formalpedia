-- Prove2me | Theorems.Thm_ModularCurve_XOneP_exists_relativeGroupLaw_isAffine_isClosedImmersion_iff_postComp_pullbackHom_eq_one_splitTorus_specialFibre_baseChange_x1_mul
-- name    : ModularCurve.XOneP.exists_relativeGroupLaw_isAffine_isClosedImmersion_iff_postComp_pullbackHom_eq_one_splitTorus_specialFibre_baseChange_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.601084+00:00
-- url     : https://prove2.me/theorems/4be556c4-9a65-528a-9cb8-55b10e4e260a
-- title:
--   Affine split torus kernel in Pic⁰ of the special fibre
-- statement:
--   Fix a prime $p$, an integer $M \ge 5$ with $p \nmid M$, a field $L$ of characteristic zero that is a cyclotomic extension of $\mathbb{Q}$ for $\{p\}$, a primitive $p$-th root of unity $\zeta \in L$, and the intermediate field $K$ of $L \subseteq \mathrm{LaurentSeries}\ L$ obtained as [`ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))`](def/ModularCurve_LaurentCoeff.html#L103); let $A$ be a discrete valuation domain with fraction field $L$ such that $p$ lies in its maximal ideal and $\zeta$ lies in the image of $A$, with $K$ an $A$-algebra compatibly, and let $j \in K$ be the element mapping to the $q$-expansion [`ModularCurve.coeffEmb L ModularCurve.jq`](def/ModularCurve_LaurentCoeff.html#L81), assumed non-zero. Write $X \to \operatorname{Spec} A$ for the two-chart model [`ModularCurve.TwoChart.modelTo A K j`](def/ModularCurve_TwoChartModel.html#L252), assumed proper, and let $k$ be an algebraically closed field of characteristic $p$ that is an $A$-algebra; the special fibre is the fibre product of $X \to \operatorname{Spec} A$ with $\operatorname{Spec} k \to \operatorname{Spec} A$, assumed reduced. Given two proper smooth geometrically integral curves $c_1 : C_1 \to \operatorname{Spec} k$, $c_2 : C_2 \to \operatorname{Spec} k$ of relative dimension $1$ with closed immersions $i_1, i_2$ into that special fibre over $\operatorname{Spec} k$ whose images cover all its points, with $\operatorname{pullback} i_1\ i_2$ reduced of cardinality $n > 0$; a section $\varepsilon$ of $X$ over $\operatorname{Spec} A$, sections $\varepsilon_1, \varepsilon_2$ of $c_1, c_2$ with $\varepsilon_1$ followed by $i_1$ equal to the base change of $\varepsilon$; a designation $D$ (a scheme with a structure morphism to $\operatorname{Spec} A$ and a zero section) that represents, with $\varepsilon$, the functor of rigidified line bundles whose fibres over algebraically closed fields are algebraically equivalent to zero, with $D.\mathrm{toBase}$ smooth and separated; the hypothesis that $D$ base-changed to $k$ represents the same functor for the special fibre with the base-changed section; designations $D_1, D_2$ representing the corresponding functors for $c_1, c_2$; and a morphism $\nu_2$ over $\operatorname{Spec} k$ from $(D.\mathrm{baseChange}\ k).\mathrm{toBase}$ to $D_2.\mathrm{toBase}$ which on every point $a$ realises the Poincaré bundle of $D_2$ as the rigidification along `rigSection c₂ t ε₂` of the pullback of $a$'s bundle along `curveChange i₂`. Then there exist a scheme $T$ with structure morphism $t_T$ to $\operatorname{Spec} k$, a relative group law $L_T$ on $t_T$, a morphism $j_T : T \to (D.\mathrm{baseChange}\ k).\mathrm{toBase}$ over $\operatorname{Spec} k$, and for every commutative $k$-algebra $R$ a bijection $e_T(R)$ from $(R^\times)^{n-1}$ to the $\operatorname{Spec} R$-points of $t_T$, such that: $T$ is affine; $j_T$ is a closed immersion; $j_T$ is a homomorphism for $L_T$ and the group law on $D.\mathrm{baseChange}\ k$ coming from the representability hypothesis and the condition `algEquivZeroGroupCut`; a point $x$ of $(D.\mathrm{baseChange}\ k).\mathrm{toBase}$ over any $k$-scheme factors through $j_T$ exactly when $x$ followed by the pullback morphism along $i_1$ is the unit point of $D_1$'s group law and $x$ followed by $\nu_2$ is the unit point of $D_2$'s group law; each $e_T(R)$ is multiplicative into $L_T$ and compatible with $k$-algebra maps $R \to R'$ by composition with the induced morphism of spectra; and, for every $k$-scheme $T'$, every pair of $T'$-points $x_1$ of $D_1.\mathrm{toBase}$ and $x_2$ of $D_2.\mathrm{toBase}$, and every point $z \in T'$, there are an open $U \ni z$ and a point $x$ of $(D.\mathrm{baseChange}\ k).\mathrm{toBase}$ over $U$ restricting to $x_1$ under the pullback morphism along $i_1$ and to $x_2$ under $\nu_2$.
--
--   This is the toric description of the relative $\mathrm{Pic}^0$ of a curve with two smooth components meeting transversally in $n$ points: the kernel of restriction to the components is a split torus of rank $n-1$, here exhibited as an affine closed subgroup scheme, and restriction is surjective in the Zariski-local sense, giving the exact sequence $1 \to \mathbb{G}_m^{\,n-1} \to \mathrm{Pic}^0(X_s) \to \mathrm{Pic}^0(C_1) \times \mathrm{Pic}^0(C_2) \to 0$ for the special fibre of the two-chart model of $X_1(Mp)$. The affineness conjunct is what allows a proper closed subscheme of the torus to be recognised as finite, and the result is used in the analysis of the $q$-divisibility of points of the special fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_exists_relativeGroupLaw_isAffine_isClosedImmersion_iff_postComp_pullbackHom_eq_one_splitTorus_specialFibre_baseChange_x1_mul.lean

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
import Definitions.Def_ModularCurve_JOnePOps
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_HopfAlgebra_FVectStructure
import Definitions.Def_HopfAlgebra_RaynaudNormalFormDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.SmoothProperCurve

theorem ModularCurve.XOneP.exists_relativeGroupLaw_isAffine_isClosedImmersion_iff_postComp_pullbackHom_eq_one_splitTorus_specialFibre_baseChange_x1_mul
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
    (D₁ : RelativePic0Designation k c₁) (hrep₁ : Nonempty (RepresentsRelSubPic c₁ ε₁ (algEquivZeroCut c₁ ε₁) D₁))
    (D₂ : RelativePic0Designation k c₂) (hrep₂ : Nonempty (RepresentsRelSubPic c₂ ε₂ (algEquivZeroCut c₂ ε₂) D₂))

    (ν₂ : SchemeHomOver (D.baseChange k).toBase D₂.toBase)
    (hν₂ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (a : SchemeHomOver t (D.baseChange k).toBase),
        Nonempty ((hrep₂.some.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a ν₂)).L ≅
          Scheme.Modules.rigidify (rigSection c₂ t ε₂) (pullback.snd c₂ t)
            ((Scheme.Modules.pullback (curveChange i₂.1 i₂.2 t)).obj (hreps.poincare.pullbackAlong a).L)))

    [IsProper (ModularCurve.TwoChart.modelTo A (↥K) j)]
    (hXred : IsReduced (pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k))) :
    ∃ (T : Scheme.{0}) (tT : T ⟶ Spec (CommRingCat.of k)) (LT : RelativeGroupLaw k tT)
      (jT : SchemeHomOver tT (D.baseChange k).toBase)
      (eT : ∀ (R : Type) [CommRing R] [Algebra k R], (Fin (n - 1) → Rˣ) ≃ SchemeHomOver (specMap k R) tT),

      IsAffine T ∧

      IsClosedImmersion jT.1 ∧
      (∀ {T' : Scheme.{0}} (s : T' ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver s tT),
        NeronModelInfra.schemeHomOverComp (LT.mul s x y) jT =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hreps).mul s
            (NeronModelInfra.schemeHomOverComp x jT) (NeronModelInfra.schemeHomOverComp y jT)) ∧

      (∀ {T' : Scheme.{0}} (t : T' ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t (D.baseChange k).toBase),
        (∃ y : SchemeHomOver t tT, NeronModelInfra.schemeHomOverComp y jT = x) ↔
          (postComp (RepresentsRelSubPic.pullbackHom i₁.1 i₁.2 hε₁ hreps hrep₁.some) x =
              (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep₁.some).one t ∧
            postComp ν₂ x = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep₂.some).one t)) ∧

      (∀ (R : Type) [CommRing R] [Algebra k R] (u v : Fin (n - 1) → Rˣ),
        eT R (u * v) = LT.mul _ (eT R u) (eT R v)) ∧
      (∀ (R R' : Type) [CommRing R] [Algebra k R] [CommRing R'] [Algebra k R'] (a : R →ₐ[k] R') (u : Fin (n - 1) → Rˣ),
        (eT R' (fun i => Units.map a.toRingHom.toMonoidHom (u i))).1 =
          Spec.map (CommRingCat.ofHom a.toRingHom) ≫ (eT R u).1) ∧

      (∀ {T' : Scheme.{0}} (t : T' ⟶ Spec (CommRingCat.of k)) (x₁ : SchemeHomOver t D₁.toBase) (x₂ : SchemeHomOver t D₂.toBase)
        (z : T'), ∃ (U : T'.Opens) (_ : z ∈ U) (x : SchemeHomOver (U.ι ≫ t) (D.baseChange k).toBase),
          (postComp (RepresentsRelSubPic.pullbackHom i₁.1 i₁.2 hε₁ hreps hrep₁.some) x).1 = U.ι ≫ x₁.1 ∧
          (postComp ν₂ x).1 = U.ι ≫ x₂.1) := by sorry
