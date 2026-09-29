-- Prove2me | Theorems.Thm_ModularCurve_forall_exists_schemeHomOver_baseChange_rat_isHom_pts_smul_of_dRModelPackage
-- name    : ModularCurve.forall_exists_schemeHomOver_baseChange_rat_isHom_pts_smul_of_dRModelPackage
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/87e1d3cb-82fc-5699-ae9a-a598fd50aa93
-- title:
--   Hecke action on the generic fibre of relative Pic⁰
-- statement:
--   Fix a prime $p$ and a package $\mathfrak X$ of Deligne–Rapoport data for the two-chart integral model `DRModel p` of the level-$p$ modular curve over $\mathbb Z$, whose structure morphism is assumed proper, together with the assumption that $\overline{\mathbb Q}$ and the function field `modularFunctionFieldBar p` form a curve (principal divisors exist, residue fields are finite over $\overline{\mathbb Q}$, and the module of Kähler differentials is free of rank one). Let $D$ consist of a scheme $P$ over $\operatorname{Spec}\mathbb Z$ with a zero section, and let $hD$ assert that $D$ represents, with respect to the section $\mathfrak X.\varepsilon_{\inf}$, the functor of rigidified line bundles that are fibrewise algebraically equivalent to zero: a Poincaré bundle satisfying that condition, a unique classifying morphism for every such bundle over any base, and triviality along the zero section. Further hypotheses: $D$ is smooth over $\mathbb Z$ with geometrically connected fibres; the analogous representability $h'$ holds for the base change to $\mathbb Q$ with the base-changed section; a $\mathbb Q$-morphism $\mathrm{aj}_{\mathbb Q}$ from the generic fibre of the model to $D_{\mathbb Q}$; a morphism $\mathrm{aj}$ from $\mathfrak X.M_\eta.C$ to $P$; a $\overline{\mathbb Q}$-point $\bar\varepsilon$ of $\mathfrak X.M_\eta.C$; a bijection $\mathrm{pts}$ from $\mathrm{Pic}^0(\overline{\mathbb Q},\,$`modularFunctionFieldBar p`$)$, the degree-zero divisor classes modulo principal ones, onto the $\overline{\mathbb Q}$-points of $D$; commutativity of the relative group law furnished by $hD$ and additivity of $\mathrm{pts}$ for it; properness of $D$ after base change to $\mathbb Z[1/p]$; an isomorphism between the Poincaré bundle of $h'$ and the transport to $\mathbb Q$ of the one of $hD$; the identity $\mathfrak X.\varepsilon_{\inf,\mathbb Q}$ followed by $\mathrm{aj}_{\mathbb Q}$ equals the zero section of $D_{\mathbb Q}$; the classifying property that for every field $K$, every $\mathbb Q$-morphism $t\colon\operatorname{Spec}K\to\operatorname{Spec}\mathbb Q$ and every $t$-point $x$ of the generic fibre curve, the pullback of the Poincaré bundle of $h'$ along $x$ followed by $\mathrm{aj}_{\mathbb Q}$ is isomorphic to the tensor product of the line bundle of the relative effective Cartier divisor of the point $x$ with the ideal module of the divisor of the cusp point $t$ followed by $\mathfrak X.\varepsilon_{\inf,\mathbb Q}$; a morphism $k_0$ from the $\overline{\mathbb Q}$-fibre to the $\mathbb Q$-fibre of the model compatible with both projections; the factorisation of $\mathrm{aj}$ through $\mathfrak X.e_\eta$, $k_0$, $\mathrm{aj}_{\mathbb Q}$ and the first projection, and the fact that $\mathrm{aj}$ lies over $\operatorname{Spec}\overline{\mathbb Q}\to\operatorname{Spec}\mathbb Z$; the compatibility of $\bar\varepsilon$ with the cusp section and the vanishing $\bar\varepsilon$ followed by $\mathrm{aj}$ equals the zero section; and finally that for every $\overline{\mathbb Q}$-point $x$ of $\mathfrak X.M_\eta.C$ there is a degree-zero divisor equal to the difference of the places attached to $x$ and to $\bar\varepsilon$ whose class is sent by $\mathrm{pts}$ to $x$ followed by $\mathrm{aj}$. Then, for the Hecke module structure `heckeModuleBar p` on $\mathrm{Pic}^0$ and every element $t$ of the Hecke algebra $\mathbb Z[T_q : q\text{ prime}]$ (realised as $\mathbb Z$-polynomials in the primes), there exists an endomorphism $\varphi_\eta$ of $D_{\mathbb Q}=D\times_{\mathbb Z}\mathbb Q$ over $\mathbb Q$ such that: for every scheme $T$ over $\mathbb Q$ and all $T$-points $x,y$ of $D_{\mathbb Q}$, composing the product of $x$ and $y$ for the base-changed relative group law with $\varphi_\eta$ equals the product of $x$ followed by $\varphi_\eta$ and $y$ followed by $\varphi_\eta$; and for every class $x$ in $\mathrm{Pic}^0$ and all $\overline{\mathbb Q}$-points $z,z_t$ of $D_{\mathbb Q}$ whose first projections are $\mathrm{pts}(x)$ and $\mathrm{pts}(t\cdot x)$ respectively, one has $z_t=z$ followed by $\varphi_\eta$.
--
--   This is the statement that Hecke correspondences on the modular curve of level $p$ induce group-law endomorphisms of the generic fibre of the relative $\mathrm{Pic}^0$ of the integral model, matching the Hecke action on degree-zero divisor classes through the Abel–Jacobi points dictionary. It is used in the construction of good Néron identity-component data for $J_0(p)$, where such generic-fibre endomorphisms are extended over the base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_forall_exists_schemeHomOver_baseChange_rat_isHom_pts_smul_of_dRModelPackage.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackage
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  ModularCurve AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve AlgebraicCurve

set_option maxHeartbeats 800000 in

theorem ModularCurve.forall_exists_schemeHomOver_baseChange_rat_isHom_pts_smul_of_dRModelPackage
    (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p) [IsProper (DRModel.toBase p)]
    [IsCurveOver (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar p)]
    (D : RelativePic0Designation ℤ (DRModel.toBase p))
    (hD : RepresentsRelSubPic (DRModel.toBase p) 𝔛.εinf (algEquivZeroCut (DRModel.toBase p) 𝔛.εinf) D)
    (hsm : Smooth D.toBase) (hconn : GeometricallyConnected D.toBase)

    (h' : RepresentsRelSubPic (baseChange ℤ (DRModel.toBase p) ℚ) (sectionBaseChange ℚ 𝔛.εinf)
          (algEquivZeroCut (baseChange ℤ (DRModel.toBase p) ℚ) (sectionBaseChange ℚ 𝔛.εinf)) (D.baseChange ℚ))
    (ajQ : SchemeHomOver (baseChange ℤ (DRModel.toBase p) ℚ) (D.baseChange ℚ).toBase)
    (aj : 𝔛.Mη.C ⟶ D.P)
    (εbar : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Mη.C // q ≫ 𝔛.Mη.toBase = 𝟙 _})
    (pts : JZero p ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))) D.toBase)
    (hcomm : (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (DRModel.toBase p) 𝔛.εinf) hD).IsCommutative)
    (pts_add : ∀ x y : JZero p, pts (x + y) =
      (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (DRModel.toBase p) 𝔛.εinf) hD).mul _ (pts x) (pts y))
    (hpa : IsProper (pullback.snd D.toBase
      (Spec.map (CommRingCat.ofHom (algebraMap ℤ (Localization.Away (p : ℤ)))))))
    (hP : Nonempty (h'.poincare.L ≅ (BaseChange.ofR (DRModel.toBase p) 𝔛.εinf ℚ
      (hD.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap ℤ ℚ), pullback.condition⟩)).L))
    (hajQε : (sectionBaseChange ℚ 𝔛.εinf).1 ≫ ajQ.1 = (D.baseChange ℚ).zeroSection)
    (haj : ∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℚ))
        (x : SchemeHomOver t (baseChange ℤ (DRModel.toBase p) ℚ)),
      Nonempty ((h'.poincare.pullbackAlong
          ⟨x.1 ≫ ajQ.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajQ.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint (baseChange ℤ (DRModel.toBase p) ℚ) x.1 x.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint (baseChange ℤ (DRModel.toBase p) ℚ) (t ≫ (sectionBaseChange ℚ 𝔛.εinf).1)
            ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange ℚ 𝔛.εinf).2).trans
              (Category.comp_id t)))).idealModule))
    (k₀ : pullback (DRModel.toBase p) (specMap ℤ (AlgebraicClosure ℚ)) ⟶ pullback (DRModel.toBase p) (specMap ℤ ℚ))
    (hk₀fst : k₀ ≫ pullback.fst (DRModel.toBase p) (specMap ℤ ℚ) = pullback.fst (DRModel.toBase p) (specMap ℤ (AlgebraicClosure ℚ)))
    (hk₀snd : k₀ ≫ pullback.snd (DRModel.toBase p) (specMap ℤ ℚ) =
      pullback.snd (DRModel.toBase p) (specMap ℤ (AlgebraicClosure ℚ)) ≫ specMap ℚ (AlgebraicClosure ℚ))
    (haj_eq : aj = 𝔛.eη ≫ k₀ ≫ ajQ.1 ≫ pullback.fst D.toBase (specMap ℤ ℚ))
    (haj_over : aj ≫ D.toBase = 𝔛.Mη.toBase ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))))
    (hεbar : εbar.1 ≫ 𝔛.eη ≫ pullback.fst (DRModel.toBase p) _ =
      Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))) ≫ 𝔛.εinf.1)
    (hajs : εbar.1 ≫ aj = Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))) ≫ D.zeroSection)
    (pts_aj : ∀ x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Mη.C // q ≫ 𝔛.Mη.toBase = 𝟙 _},
      ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar p)),
        (Dv : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar p)) =
          Finsupp.single (𝔛.Mη.pointEquivPlace x) 1 - Finsupp.single (𝔛.Mη.pointEquivPlace εbar) 1 ∧
        (pts (Pic0.mk Dv)).1 = x.1 ≫ aj) :

    letI := heckeModuleBar p
    ∀ t : HeckeAlg,
      ∃ φη : SchemeHomOver
          (pullback.snd D.toBase (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))))
          (pullback.snd D.toBase (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ)))),
        (∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of ℚ))
            (x y : SchemeHomOver s (pullback.snd D.toBase (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))))),
          NeronModelInfra.schemeHomOverComp
              (((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (DRModel.toBase p) 𝔛.εinf) hD).baseChange
                  (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ)))).mul s x y) φη =
            ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (DRModel.toBase p) 𝔛.εinf) hD).baseChange
                (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ)))).mul s
              (NeronModelInfra.schemeHomOverComp x φη) (NeronModelInfra.schemeHomOverComp y φη)) ∧
        (∀ (x : JZero p)
            (z zt : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶
              pullback D.toBase (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ)))),
          z ≫ pullback.fst D.toBase _ = (pts x).1 → zt ≫ pullback.fst D.toBase _ = (pts (t • x)).1 → zt = z ≫ φη.1) := by sorry
