-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_exists_hom_mul_and_pts_heckeOperatorHAlong_self_eq_comp
-- name    : ModularCurve.XHDRModelAtP.exists_hom_mul_and_pts_heckeOperatorHAlong_self_eq_comp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/e5aeeeb4-5631-5ae3-996f-5c05c8a58230
-- title:
--   Uₚ at p ∥ M as a group endomorphism of Pic⁰
-- statement:
--   Fix a prime $p$ and a level $M$ with $p \mid M$ but $p^2 \nmid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit that becomes $1$ in $(\mathbb{Z}/(M/p))^\times$, and the hypothesis `hj` that $j$, as the Laurent series `jqModC ℚ`, lies in the $q$-expansion function field of $\mathrm{SL}(2,\mathbb{Z})$; let $\mathfrak{X}$ be a Deligne–Rapoport datum `XHDRModelAtP p M H hpM hj` for $X_H(M)$ over the base ring $R_p$, with `toBase` proper. The further data are: an $\overline{\mathbb{Q}}$-algebra automorphism $\theta$ of $\overline{\mathbb{Q}}(X_H(M))$ (the field `xHFunctionFieldBar M H`) which on Laurent series sends any element agreeing with an element $u$ of `xHFunctionFieldBar (M/p) (infSubgroup p M H hpM)` to `qExpand` of $u$ at $p$, i.e. to $u(q^p)$; the compatibility `hwgen` saying that whenever two $\overline{\mathbb{Q}}$-points of $\mathfrak{X}.\mathrm{Meta}.C$ correspond under the isomorphism $\mathfrak{X}.w$ (read through $\mathfrak{X}.\mathrm{eeta}$ and the first projection), the associated places satisfy $\mathrm{pointEquivPlace}\,y' = \mathrm{ofAlgAut}(\theta)\cdot \mathrm{pointEquivPlace}\,y$; a relative $\mathrm{Pic}^0$ designation $D$ over $\operatorname{Spec} R_p$ together with a proof `hD` that it represents the rigidified line bundles on $(\mathfrak{X}, \varepsilon_\infty)$ that are fibrewise algebraically trivial, with $D \to \operatorname{Spec} R_p$ smooth, separated, quasi-compact, surjective and geometrically connected; the corresponding representability `hDQ` after base change to $\mathbb{Q}$, together with an isomorphism `hPQ` of its Poincaré bundle with the base change of the pullback of the Poincaré bundle of `hD`; an Abel–Jacobi morphism $a_{\mathbb{Q}}$ over $\mathbb{Q}$ killing $\varepsilon_\infty$ and classifying, on points over any field, the class of $[x] - [\varepsilon_\infty]$ (the line bundle of the relative effective Cartier divisor of $x$ tensored with the ideal module of that of $\varepsilon_\infty$); a morphism $k_{\mathbb{Q}}$ from the $\overline{\mathbb{Q}}$-fibre to the $\mathbb{Q}$-fibre compatible with both projections up to $\operatorname{Spec}\overline{\mathbb{Q}} \to \operatorname{Spec}\mathbb{Q}$; the induced $\bar a = \mathfrak{X}.\mathrm{eeta} \mathbin{;} k_{\mathbb{Q}} \mathbin{;} a_{\mathbb{Q}} \mathbin{;} \mathrm{pullback.fst}$ lying over the generic point, a $\overline{\mathbb{Q}}$-point $\bar\varepsilon$ sitting at $\varepsilon_\infty$ and sent by $\bar a$ to the zero section; and finally a bijection $\mathrm{pts}$ from $J_H(M) = \mathrm{Pic}^0(\overline{\mathbb{Q}}(X_H(M)))$ onto the $\overline{\mathbb{Q}}$-points of $D$ which is additive for the relative group law supplied by `hD`, Galois-equivariant, and pinned by Abel–Jacobi in the sense that for $\overline{\mathbb{Q}}$-points $x$ and $s$ with $s$ at $\varepsilon_\infty$ there is a degree-zero divisor equal to $(x) - (s)$ whose class is sent by $\mathrm{pts}$ to $x$ followed by $\bar a$. The conclusion asserts the existence of an endomorphism $\varphi$ of $D.P$ over $\operatorname{Spec} R_p$ such that, for every scheme $T$ with a morphism $s$ to `base p` and all points $x, y$ of $D$ over $s$, composing the group-law product of $x$ and $y$ with $\varphi$ equals the product of $x \mathbin{;} \varphi$ and $y \mathbin{;} \varphi$, and such that for every $x \in J_H(M)$ one has $\mathrm{pts}(\,$`heckeOperatorHAlong`$\,\overline{\mathbb{Q}}\,M\,H\,p\,(x)) = \mathrm{pts}(x)$ followed by $\varphi$.
--
--   This is the statement that the Hecke operator $U_p$ at the prime $p$ exactly dividing the level, acting on $\mathrm{Pic}^0$ of $X_H(M)$ over $\overline{\mathbb{Q}}$, is induced by a single group-law-preserving endomorphism of the scheme over $\mathbb{Z}_{(p)}$ representing the relative $\mathrm{Pic}^0$ of the Deligne–Rapoport model, the Atkin–Lehner involution entering through the automorphism $\theta$ realising $q \mapsto q^p$. It feeds the Hecke data of the construction of the Néron-type object for $J_H$ at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_exists_hom_mul_and_pts_heckeOperatorHAlong_self_eq_comp.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_XHHeckeOperator
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve
  IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP
  AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve
open scoped MatrixGroups
set_option maxHeartbeats 400000 in

theorem ModularCurve.XHDRModelAtP.exists_hom_mul_and_pts_heckeOperatorHAlong_self_eq_comp
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    [IsProper (toBase p (ΓM M H) hj)]

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hθ : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ∀ (f : ↥(xHFunctionFieldBar M H)) (u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))), (f : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) →
        ((θ f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)
    (D : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))
    (hD : RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) D)
    (hsm : Smooth D.toBase) (hsep : IsSeparated D.toBase) (hqc : QuasiCompact D.toBase)
    (hsurj : Surjective D.toBase) (hgc : GeometricallyConnected D.toBase)

    (hDQ : RepresentsRelSubPic (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (sectionBaseChange ℚ 𝔛.εinf)
        (algEquivZeroCut (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (sectionBaseChange ℚ 𝔛.εinf)) (D.baseChange ℚ))
    (hPQ : Nonempty (hDQ.poincare.L ≅ (BaseChange.ofR (toBase p (ΓM M H) hj) 𝔛.εinf ℚ
        (hD.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap (R p) ℚ), pullback.condition⟩)).L))

    (ajQ : SchemeHomOver (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (D.baseChange ℚ).toBase)
    (hajQε : (sectionBaseChange ℚ 𝔛.εinf).1 ≫ ajQ.1 = (D.baseChange ℚ).zeroSection)
    (hajQ : ∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℚ))
        (x : SchemeHomOver t (baseChange (R p) (toBase p (ΓM M H) hj) ℚ)),
      Nonempty ((hDQ.poincare.pullbackAlong
          ⟨x.1 ≫ ajQ.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajQ.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) x.1 x.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (t ≫ (sectionBaseChange ℚ 𝔛.εinf).1)
            ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange ℚ 𝔛.εinf).2).trans
              (Category.comp_id t)))).idealModule))

    (kQ : pullback (toBase p (ΓM M H) hj) (genPt p) ⟶ pullback (toBase p (ΓM M H) hj) (specMap (R p) ℚ))
    (hkQ₁ : kQ ≫ pullback.fst (toBase p (ΓM M H) hj) (specMap (R p) ℚ) = pullback.fst (toBase p (ΓM M H) hj) (genPt p))
    (hkQ₂ : kQ ≫ pullback.snd (toBase p (ΓM M H) hj) (specMap (R p) ℚ) = pullback.snd (toBase p (ΓM M H) hj) (genPt p) ≫ specMap ℚ (AlgebraicClosure ℚ))

    (ajbar : 𝔛.Meta.C ⟶ D.P) (hajbar : ajbar = 𝔛.eeta ≫ kQ ≫ ajQ.1 ≫ pullback.fst D.toBase (specMap (R p) ℚ))
    (hajbar_over : ajbar ≫ D.toBase = 𝔛.Meta.toBase ≫ genPt p)
    (εbar : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
    (hεbar : εbar.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1)
    (hεbar_aj : εbar.1 ≫ ajbar = genPt p ≫ D.zeroSection)

    (pts : JH M H ≃ SchemeHomOver (genPt p) D.toBase)
    (hpts_add : ∀ x y : JH M H,
      pts (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul _ (pts x) (pts y))
    (hpts_galois : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : JH M H),
      (pts (σ • x)).1 = Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ (pts x).1)
    (hpts_aj : ∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      s.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1 →
      ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)),
        (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
          Finsupp.single (𝔛.Meta.pointEquivPlace x) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace s) 1 ∧
        (pts (Pic0.mk Dv)).1 = x.1 ≫ ajbar) :
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    ∃ φ : SchemeHomOver D.toBase D.toBase,
      (∀ {T : Scheme.{0}} (s : T ⟶ base p) (x y : SchemeHomOver s D.toBase),
        NeronModelInfra.schemeHomOverComp
            ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul s x y) φ =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul s
            (NeronModelInfra.schemeHomOverComp x φ) (NeronModelInfra.schemeHomOverComp y φ)) ∧
      ∀ x : JH M H, (pts (heckeOperatorHAlong (AlgebraicClosure ℚ) M H p x)).1 = (pts x).1 ≫ φ.1 := by sorry
