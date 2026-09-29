-- Prove2me | Theorems.Thm_ModularCurve_XOneP_exists_relativeGroupLaw_isClosedImmersion_iff_postComp_pullbackHom_eq_one_splitTorus_specialFibre_baseChange_x1_mul
-- name    : ModularCurve.XOneP.exists_relativeGroupLaw_isClosedImmersion_iff_postComp_pullbackHom_eq_one_splitTorus_specialFibre_baseChange_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.601084+00:00
-- url     : https://prove2.me/theorems/890b2dfc-bb66-5ee1-94af-a59da8f8469e
-- title:
--   Kernel of special-fibre Picard projections: a split torus of rank n-1
-- statement:
--   Fix a prime $p$, an integer $M\ge 5$ with $p\nmid M$, a field $L$ of characteristic zero that is a cyclotomic extension of $\mathbb{Q}$ of type $\{p\}$, a primitive $p$-th root of unity $\zeta\in L$, and the intermediate field $K$ of $L((q))$ obtained as [`ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))`](def/ModularCurve_LaurentCoeff.html#L103), i.e. the field generated over $L$ by the coefficientwise image of the $q$-expansion function field of $\Gamma_1(Mp)$; let $A$ be a discrete valuation domain with fraction field $L$, with $p$ in its maximal ideal and $\zeta$ in its image, made an $A$-algebra structure on $K$ compatibly, and let $j\in K$ be a nonzero element whose image in $L((q))$ is the $q$-expansion [`ModularCurve.jq`](def/ModularCurve_X0.html#L157); write $X=$ [`ModularCurve.TwoChart.modelTo A K j`](def/ModularCurve_TwoChartModel.html#L252) for the two-chart model over $\operatorname{Spec} A$, assumed proper. Let $k$ be an algebraically closed $A$-algebra field of characteristic $p$ and $X_s=X\times_A k$, assumed reduced. Let $c_1,c_2$ be proper smooth of relative dimension $1$ and geometrically integral over $k$, with closed immersions $i_1,i_2$ into $X_s$ over $k$ whose images together cover all points of $X_s$, such that $C_1\times_{X_s}C_2$ is reduced with exactly $n>0$ points, $n>0$. Let $\varepsilon$ be a section of $X$ over $A$ and $\varepsilon_1,\varepsilon_2$ sections of $c_1,c_2$ with $\varepsilon_1$ followed by $i_1$ equal to the base-changed section. Let $D$ be a relative $\operatorname{Pic}^0$ designation for $X$ with a representing datum for the fibrewise algebraically-trivial cut and with $D.\mathrm{toBase}$ smooth and separated; let `hreps` be such a representing datum for $D.\mathrm{baseChange}\,k$ over $X_s$, and $D_1,D_2$ designations with representing data for $c_1,c_2$. Finally let $\nu_2$ be a morphism $D_s=(D.\mathrm{baseChange}\,k).\mathrm{toBase}\to D_2.\mathrm{toBase}$ over $k$ such that for every $k$-scheme $t$ and every $t$-point $a$ of $D_s$ the pullback of the Poincaré bundle of $D_2$ along $a$ followed by $\nu_2$ is isomorphic to the rigidification along `rigSection c₂ t ε₂` of the pullback, along `curveChange i₂.1`, of the bundle classified by $a$. Then there exist a scheme $T$ over $k$ with structure morphism $t_T$, a relative group law $L_T$ on $t_T$, a morphism $j_T:T\to D_s$ over $k$, and for every commutative $k$-algebra $R$ a bijection $e_T(R):(R^\times)^{n-1}\to T(R)$, such that: $j_T$ is a closed immersion; $j_T$ is a homomorphism, i.e. $L_T.\mathrm{mul}$ followed by $j_T$ agrees with the group law on $D_s$ coming from `hreps` and `algEquivZeroGroupCut`; for every $k$-scheme $t$, a $t$-point $x$ of $D_s$ factors through $j_T$ if and only if both `RepresentsRelSubPic.pullbackHom i₁.1 …` and $\nu_2$ carry $x$ to the unit points of the group laws on $D_1.\mathrm{toBase}$ and $D_2.\mathrm{toBase}$; each $e_T(R)$ is multiplicative; the family $e_T$ is natural, in that for a $k$-algebra map $a:R\to R'$ the point $e_T(R')$ of the componentwise image of $u$ is $\operatorname{Spec}(a)$ followed by $e_T(R)(u)$; and the pair of projections is locally jointly surjective: for all $t:T'\to\operatorname{Spec} k$, $t$-points $x_1$ of $D_1.\mathrm{toBase}$ and $x_2$ of $D_2.\mathrm{toBase}$, and every $z\in T'$, there is an open $U\ni z$ and a point $x$ of $D_s$ over $U$ whose images under the two projections are the restrictions of $x_1$ and $x_2$ to $U$.
--
--   This is the exact sequence $1\to\mathbb{G}_m^{\,n-1}\to\operatorname{Pic}^0(X_s)\to\operatorname{Pic}^0(C_1)\times\operatorname{Pic}^0(C_2)\to 0$ for the special fibre of the model of $X_1(Mp)$ at $p$, a curve with two smooth components meeting transversally in $n$ points, here with the representing datum of the rigidified relative $\operatorname{Pic}^0$ bound explicitly so that the torus, the group law and the projections are keyed to one and the same witness. It feeds the description of the special fibre of the Néron model of the Jacobian of $X_1(Mp)$ and the Hecke- and Galois-equivariant statements about it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_exists_relativeGroupLaw_isClosedImmersion_iff_postComp_pullbackHom_eq_one_splitTorus_specialFibre_baseChange_x1_mul.lean

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

theorem ModularCurve.XOneP.exists_relativeGroupLaw_isClosedImmersion_iff_postComp_pullbackHom_eq_one_splitTorus_specialFibre_baseChange_x1_mul
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
