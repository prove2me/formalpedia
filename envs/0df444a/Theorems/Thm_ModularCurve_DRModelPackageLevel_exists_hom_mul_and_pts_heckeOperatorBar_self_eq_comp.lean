-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_exists_hom_mul_and_pts_heckeOperatorBar_self_eq_comp
-- name    : ModularCurve.DRModelPackageLevel.exists_hom_mul_and_pts_heckeOperatorBar_self_eq_comp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/ab9e5f2a-5a97-59d1-b58c-770ef619333f
-- title:
--   Uₚ on J₀(N₀p) induced by an endomorphism of D
-- statement:
--   Let $N_0\ge 1$ and let $p$ be a prime with $p\nmid N_0$, and let $\mathfrak P$ be a Deligne–Rapoport package `DRModelPackageLevel N₀ p hpN₀` for the Igusa model $X=X(N_0,p)$ over $R=R\,p$, whose structure morphism `toBase N₀ p` is proper. Assume given: a relative $\mathrm{Pic}^0$ designation $D$ for this curve (a scheme $D.P$ over $\operatorname{Spec} R$ with a zero section) together with data `hD` exhibiting $D$, via a Poincaré bundle, as representing the functor of $\mathfrak P.\varepsilon_{\mathrm{inf}}$-rigidified line bundles on $X$ that are fibrewise algebraically equivalent to zero; that $D.\mathrm{toBase}$ is smooth, separated, quasi-compact, surjective and geometrically connected; the corresponding representability `hDQ` over $\mathbb Q$ for the base change $D\times_R\mathbb Q$ with the base-changed section, together with an isomorphism `hPQ` of its Poincaré bundle with the one obtained from that of `hD` by base change; an Abel–Jacobi morphism $aj_{\mathbb Q}$ from $X_{\mathbb Q}$ to $(D\times_R\mathbb Q).P$ over $\operatorname{Spec}\mathbb Q$ sending the cusp section to the zero section, and classifying, for every field $K$, every $t:\operatorname{Spec}K\to\operatorname{Spec}\mathbb Q$ and every $K$-point $x$ of $X_{\mathbb Q}$ over $t$, the line bundle of the relative effective Cartier divisor of $x$ tensored with the ideal module of the divisor of $t\circ\varepsilon_{\mathrm{inf},\mathbb Q}$; a morphism $k_{\mathbb Q}$ from $X\times_R\overline{\mathbb Q}$ to $X\times_R\mathbb Q$ compatible with the projections and with $\operatorname{Spec}\overline{\mathbb Q}\to\operatorname{Spec}\mathbb Q$; the composite $\overline{aj}:\mathfrak P.\mathrm{Meta}.C\to D.P$ of $\mathfrak P.\mathrm{eeta}$, $k_{\mathbb Q}$, $aj_{\mathbb Q}$ and the first projection, lying over `genPt p`; a $\overline{\mathbb Q}$-point $\bar\varepsilon$ of $\mathfrak P.\mathrm{Meta}.C$ mapping to the cusp $\mathfrak P.\varepsilon_{\mathrm{inf}}$ and sent by $\overline{aj}$ to the zero section; and a bijection $\mathrm{pts}$ from $\mathrm{Pic}^0$ of the function field `modularFunctionFieldBar (N₀ * p)` over $\overline{\mathbb Q}$ to the $\overline{\mathbb Q}$-points of $D$ over `genPt p`, which is additive for the relative group law that `hD` induces, is equivariant for $\operatorname{Gal}(\overline{\mathbb Q}/\mathbb Q)$, and satisfies: for all $\overline{\mathbb Q}$-points $x,s$ of $\mathfrak P.\mathrm{Meta}.C$ with $s$ the cusp, there is a degree-zero divisor equal to $(x)-(s)$ in the places of the function field whose class is sent by $\mathrm{pts}$ to $x$ followed by $\overline{aj}$. The conclusion is that there exists an endomorphism $\varphi$ of $D.P$ over $\operatorname{Spec} R$ which is a homomorphism for the relative group law on $T$-valued points, for every scheme $T$ and every $s:T\to$ `base p` and all $x,y$ over $s$, and which induces the $p$-th Hecke operator: for every $x$ in $\mathrm{Pic}^0$, $\mathrm{pts}(\,$`heckeOperatorBar (N₀ * p) ⟨p, _⟩`$\,x)$ equals $\mathrm{pts}(x)$ followed by $\varphi$.
--
--   This is the statement that the operator $U_p$ on $J_0(N_0p)(\overline{\mathbb Q})$ is realised by a group-law endomorphism of the scheme representing the relative $\mathrm{Pic}^0$ of the Deligne–Rapoport model over $\mathbb Z_{(p)}$, the case $\ell=p$ being the one not covered by the correspondence construction at levels prime to $p$. It feeds [`ModularCurve.DRModelPackageLevel.forall_heckeAlg_exists_hom_mul_and_pts_smul_eq_comp`](thm.html#ModularCurve.DRModelPackageLevel.forall_heckeAlg_exists_hom_mul_and_pts_smul_eq_comp), where the whole Hecke algebra is realised on $D$; the argument proceeds through the Atkin–Lehner relation $U_p+w_p=\beta^*\alpha_*$ together with the degeneracy and Atkin–Lehner endomorphisms supplied by the cited results.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_exists_hom_mul_and_pts_heckeOperatorBar_self_eq_comp.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_ModularCurve_ArithmeticGalois
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
  ModularCurve ModularCurve.DRLevel ModularCurve.JZeroNeronObjectAtP AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve AlgebraicCurve

theorem ModularCurve.DRModelPackageLevel.exists_hom_mul_and_pts_heckeOperatorBar_self_eq_comp
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀) (𝔓 : DRModelPackageLevel N₀ p hpN₀)
    [IsProper (toBase N₀ p)]

    (D : RelativePic0Designation (R p) (toBase N₀ p))
    (hD : RepresentsRelSubPic (toBase N₀ p) 𝔓.εinf (algEquivZeroCut (toBase N₀ p) 𝔓.εinf) D)
    (hsm : Smooth D.toBase) (hsep : IsSeparated D.toBase) (hqc : QuasiCompact D.toBase)
    (hsurj : Surjective D.toBase) (hgc : GeometricallyConnected D.toBase)

    (hDQ : RepresentsRelSubPic (baseChange (R p) (toBase N₀ p) ℚ) (sectionBaseChange ℚ 𝔓.εinf)
        (algEquivZeroCut (baseChange (R p) (toBase N₀ p) ℚ) (sectionBaseChange ℚ 𝔓.εinf)) (D.baseChange ℚ))
    (hPQ : Nonempty (hDQ.poincare.L ≅ (BaseChange.ofR (toBase N₀ p) 𝔓.εinf ℚ
        (hD.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap (R p) ℚ), pullback.condition⟩)).L))

    (ajQ : SchemeHomOver (baseChange (R p) (toBase N₀ p) ℚ) (D.baseChange ℚ).toBase)
    (hajQε : (sectionBaseChange ℚ 𝔓.εinf).1 ≫ ajQ.1 = (D.baseChange ℚ).zeroSection)
    (hajQ : ∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℚ))
        (x : SchemeHomOver t (baseChange (R p) (toBase N₀ p) ℚ)),
      Nonempty ((hDQ.poincare.pullbackAlong
          ⟨x.1 ≫ ajQ.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajQ.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase N₀ p) ℚ) x.1 x.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase N₀ p) ℚ) (t ≫ (sectionBaseChange ℚ 𝔓.εinf).1)
            ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange ℚ 𝔓.εinf).2).trans
              (Category.comp_id t)))).idealModule))

    (kQ : pullback (toBase N₀ p) (genPt p) ⟶ pullback (toBase N₀ p) (specMap (R p) ℚ))
    (hkQ₁ : kQ ≫ pullback.fst (toBase N₀ p) (specMap (R p) ℚ) = pullback.fst (toBase N₀ p) (genPt p))
    (hkQ₂ : kQ ≫ pullback.snd (toBase N₀ p) (specMap (R p) ℚ) = pullback.snd (toBase N₀ p) (genPt p) ≫ specMap ℚ (AlgebraicClosure ℚ))

    (ajbar : 𝔓.Meta.C ⟶ D.P) (hajbar : ajbar = 𝔓.eeta ≫ kQ ≫ ajQ.1 ≫ pullback.fst D.toBase (specMap (R p) ℚ))
    (hajbar_over : ajbar ≫ D.toBase = 𝔓.Meta.toBase ≫ genPt p)
    (εbar : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _})
    (hεbar : εbar.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p) = genPt p ≫ 𝔓.εinf.1) (hεbar_aj : εbar.1 ≫ ajbar = genPt p ≫ D.zeroSection)

    (pts : JZero (N₀ * p) ≃ SchemeHomOver (genPt p) D.toBase)
    (hpts_add : ∀ x y : JZero (N₀ * p),
      pts (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul _ (pts x) (pts y))
    (hpts_galois : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : JZero (N₀ * p)),
      (pts (σ • x)).1 = Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ (pts x).1)
    (hpts_aj : ∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _}),
      s.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p) = genPt p ≫ 𝔓.εinf.1 →
      ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar (N₀ * p)),
        (Dv : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N₀ * p))) =
          Finsupp.single (𝔓.Meta.pointEquivPlace x) 1 - Finsupp.single (𝔓.Meta.pointEquivPlace s) 1 ∧
        (pts (Pic0.mk Dv)).1 = x.1 ≫ ajbar) :
    ∃ φ : SchemeHomOver D.toBase D.toBase,
      (∀ {T : Scheme.{0}} (s : T ⟶ base p) (x y : SchemeHomOver s D.toBase),
        NeronModelInfra.schemeHomOverComp
            ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul s x y) φ =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul s
            (NeronModelInfra.schemeHomOverComp x φ) (NeronModelInfra.schemeHomOverComp y φ)) ∧
      ∀ x : JZero (N₀ * p), (pts (heckeOperatorBar (N₀ * p) ⟨p, Fact.out⟩ x)).1 = (pts x).1 ≫ φ.1 := by sorry
