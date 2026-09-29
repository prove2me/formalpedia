-- Prove2me | Theorems.Thm_ModularCurve_XOneP_existsUnique_schemeHomOver_prodStr_comp_eq_of_comp_splitTorus_eq_one_specialFibre_baseChange_x1_mul
-- name    : ModularCurve.XOneP.existsUnique_schemeHomOver_prodStr_comp_eq_of_comp_splitTorus_eq_one_specialFibre_baseChange_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.601084+00:00
-- url     : https://prove2.me/theorems/d8b62818-ec5e-512a-a76f-e4cb7ec9efdd
-- title:
--   Unique homomorphic factorisation through D₁×_k D₂
-- statement:
--   Fix a prime $p$ and an integer $M\ge 5$ not divisible by $p$; let $L$ be a field of characteristic zero which is a $\{p\}$-cyclotomic extension of $\mathbb{Q}$, $\zeta\in L$ a primitive $p$-th root of unity, and $K$ the intermediate field of $L\subseteq L((q))$ obtained by adjoining to $L$ the coefficientwise images of the elements of [`ModularCurve.x1FunctionField (M * p)`](def/ModularCurve_X1.html#L137); let $A$ be a discrete valuation ring with fraction field $L$, with $p$ in its maximal ideal and $\zeta$ in the image of $A$, acting compatibly on $K$, and let $j\in K$ be a nonzero element whose image in $L((q))$ is the coefficientwise image of the $q$-expansion [`ModularCurve.jq`](def/ModularCurve_X0.html#L157). Write $x$ for the two-chart model [`ModularCurve.TwoChart.modelTo A K j`](def/ModularCurve_TwoChartModel.html#L252) over $\operatorname{Spec}A$, assumed proper, and let $k$ be an algebraically closed $A$-field of characteristic $p$ with reduced special fibre $X_k=x\times_{\operatorname{Spec}A}\operatorname{Spec}k$. Let $c_1,c_2$ be proper, smooth of relative dimension $1$ and geometrically integral $k$-schemes with closed immersions $i_1,i_2$ into $X_k$ over $k$ whose images cover $X_k$, such that $C_1\times_{X_k}C_2$ is reduced with exactly $n>0$ points. Let $\varepsilon$ be a section of $x$ and $\varepsilon_1,\varepsilon_2$ sections of $c_1,c_2$ with $\varepsilon_1$ followed by $i_1$ the base change of $\varepsilon$. Let $D$ be a relative $\mathrm{Pic}^0$ designation for $x$ (a scheme over $\operatorname{Spec}A$ with a zero section) representing, with Poincaré bundle, the functor of $\varepsilon$-rigidified line bundles that are fibrewise algebraically equivalent to zero, with $D.toBase$ smooth and separated; assume the base change $D_k$ represents the corresponding functor for $X_k$ and the base-changed section, and let $D_1,D_2$ represent the corresponding functors for $(c_1,\varepsilon_1)$, $(c_2,\varepsilon_2)$. Write $\nu_1$ for the morphism `RepresentsRelSubPic.pullbackHom` classifying pullback of the Poincaré bundle of $D_k$ along $i_1$, and let $\nu_2: D_k\to D_2$ be a $k$-morphism which, on every $T$-point $a$, carries the Poincaré bundle of $D_2$ pulled back along $a$ followed by $\nu_2$ to the rigidification of the $i_2$-pullback of the bundle classified by $a$. Let $t_T$ be a $k$-scheme with a relative group law $L_T$, together with bijections, multiplicative and natural in $R$, between $(\mathrm{Fin}(n-1)\to R^\times)$ and its $R$-points, and a closed immersion $j_T:t_T\to D_k$ which is a homomorphism for $L_T$ and the group law on $D_k$ coming from representability, and whose points are exactly the points $x$ of $D_k$ with $\nu_1x$ and $\nu_2x$ both trivial; assume furthermore that $(\nu_1,\nu_2)$ is Zariski-locally surjective on points: any pair $(x_1,x_2)$ of $T'$-points of $D_1,D_2$ is, near each point of $T'$, of the form $(\nu_1x,\nu_2x)$. Finally let $g_Y$ be a separated $k$-scheme with a relative group law $L_Y$ and let $\psi:D_k\to Y$ be a $k$-morphism which is a homomorphism and whose composite with $j_T$ is the identity section of $L_Y$. Then there is a unique $k$-morphism $\bar\psi$ from $D_1\times_k D_2$ (with structure map `prodStr`) to $Y$ such that $x$ followed by $\psi$ equals the point $(\nu_1x,\nu_2x)$ followed by $\bar\psi$ for every point $x$ of $D_k$ over any $k$-scheme, and such that $\bar\psi$ is a homomorphism from the product of the group laws on $D_1$ and $D_2$ to $L_Y$.
--
--   This is the factorisation step for the special fibre of the relative $\mathrm{Pic}^0$ of the two-chart model of $X_1(Mp)$ in characteristic $p$: a homomorphism out of that special fibre killing the gluing torus descends uniquely, and homomorphically, along the pair of restriction maps to the Jacobians of the two components. It is used in the construction of the norm-free part, [`ModularCurve.XOneP.exists_isClosedImmersion_isProper_smooth_normFreePart_of_representsRelSubPic_twoChartModel_x1_mul`](thm.html#ModularCurve.XOneP.exists_isClosedImmersion_isProper_smooth_normFreePart_of_representsRelSubPic_twoChartModel_x1_mul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_existsUnique_schemeHomOver_prodStr_comp_eq_of_comp_splitTorus_eq_one_specialFibre_baseChange_x1_mul.lean

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
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawProd

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.SmoothProperCurve

theorem ModularCurve.XOneP.existsUnique_schemeHomOver_prodStr_comp_eq_of_comp_splitTorus_eq_one_specialFibre_baseChange_x1_mul
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
    (hXred : IsReduced (pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)))

    (T : Scheme.{0}) (tT : T ⟶ Spec (CommRingCat.of k)) (LT : RelativeGroupLaw k tT)
    (jT : SchemeHomOver tT (D.baseChange k).toBase)
    (eT : ∀ (R : Type) [CommRing R] [Algebra k R], (Fin (n - 1) → Rˣ) ≃ SchemeHomOver (specMap k R) tT)
    (hjT : IsClosedImmersion jT.1)
    (hjTmul : ∀ {T' : Scheme.{0}} (s : T' ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver s tT),
        NeronModelInfra.schemeHomOverComp (LT.mul s x y) jT =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hreps).mul s
            (NeronModelInfra.schemeHomOverComp x jT) (NeronModelInfra.schemeHomOverComp y jT))
    (hker : ∀ {T' : Scheme.{0}} (t : T' ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t (D.baseChange k).toBase),
        (∃ y : SchemeHomOver t tT, NeronModelInfra.schemeHomOverComp y jT = x) ↔
          (postComp (RepresentsRelSubPic.pullbackHom i₁.1 i₁.2 hε₁ hreps hrep₁.some) x =
              (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep₁.some).one t ∧
            postComp ν₂ x = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep₂.some).one t))
    (heT_mul : ∀ (R : Type) [CommRing R] [Algebra k R] (u v : Fin (n - 1) → Rˣ),
        eT R (u * v) = LT.mul _ (eT R u) (eT R v))
    (heT_nat : ∀ (R R' : Type) [CommRing R] [Algebra k R] [CommRing R'] [Algebra k R'] (a : R →ₐ[k] R') (u : Fin (n - 1) → Rˣ),
        (eT R' (fun i => Units.map a.toRingHom.toMonoidHom (u i))).1 =
          Spec.map (CommRingCat.ofHom a.toRingHom) ≫ (eT R u).1)
    (hepi : ∀ {T' : Scheme.{0}} (t : T' ⟶ Spec (CommRingCat.of k)) (x₁ : SchemeHomOver t D₁.toBase) (x₂ : SchemeHomOver t D₂.toBase)
        (z : T'), ∃ (U : T'.Opens) (_ : z ∈ U) (x : SchemeHomOver (U.ι ≫ t) (D.baseChange k).toBase),
          (postComp (RepresentsRelSubPic.pullbackHom i₁.1 i₁.2 hε₁ hreps hrep₁.some) x).1 = U.ι ≫ x₁.1 ∧
          (postComp ν₂ x).1 = U.ι ≫ x₂.1)

    (Y : Scheme.{0}) (gY : Y ⟶ Spec (CommRingCat.of k)) [IsSeparated gY] (LY : RelativeGroupLaw k gY)
    (ψ : SchemeHomOver (D.baseChange k).toBase gY)

    (hψmul : ∀ {T' : Scheme.{0}} (s : T' ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver s (D.baseChange k).toBase),
        NeronModelInfra.schemeHomOverComp
            ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hreps).mul s x y) ψ =
          LY.mul s (NeronModelInfra.schemeHomOverComp x ψ) (NeronModelInfra.schemeHomOverComp y ψ))

    (hψT : ∀ {T' : Scheme.{0}} (t : T' ⟶ Spec (CommRingCat.of k)) (y : SchemeHomOver t tT),
        NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp y jT) ψ = LY.one t) :
    ∃! ψbar : SchemeHomOver (prodStr D₁.toBase D₂.toBase) gY,

      (∀ {T' : Scheme.{0}} (t : T' ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t (D.baseChange k).toBase),
        NeronModelInfra.schemeHomOverComp x ψ =
          NeronModelInfra.schemeHomOverComp
            (prodPairPt (postComp (RepresentsRelSubPic.pullbackHom i₁.1 i₁.2 hε₁ hreps hrep₁.some) x) (postComp ν₂ x)) ψbar) ∧

      (∀ {T' : Scheme.{0}} (s : T' ⟶ Spec (CommRingCat.of k)) (a b : SchemeHomOver s (prodStr D₁.toBase D₂.toBase)),
        NeronModelInfra.schemeHomOverComp
            (((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep₁.some).prod
              (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep₂.some)).mul s a b) ψbar =
          LY.mul s (NeronModelInfra.schemeHomOverComp a ψbar) (NeronModelInfra.schemeHomOverComp b ψbar)) := by sorry
