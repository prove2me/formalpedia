-- Prove2me | Theorems.Thm_ModularCurve_JHNeronObjectAtP_resPt_comp_eq_of_resPt_comp_eq_of_pts_smul_atkinLehner_of_abelJacobiPin
-- name    : ModularCurve.JHNeronObjectAtP.resPt_comp_eq_of_resPt_comp_eq_of_pts_smul_atkinLehner_of_abelJacobiPin
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/44347e55-eb79-5316-91a6-aae15751ad5d
-- title:
--   Reduction of an Atkin–Lehner translate depends only on the reduction
-- statement:
--   Fix a prime $p$, an integer $M \ge 1$ with $p \mid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$, and a valuation subring $Pl$ of an algebraic closure of $\mathbb{Q}$ with $p$ a non-unit of $Pl$ and residue field algebraically closed of characteristic $p$; assume $j$, as a $q$-expansion, lies in the full-level function field (`hj`). Let $\mathfrak{X}$ be a model datum `XHDRModelAtP p M H hpM hj` for $X_H(M)$ over $R p$ with cusp section $\mathfrak{X}.\varepsilon_{\inf}$, curve model $\mathfrak{X}.\mathrm{Meta}$ of the geometric function field $\mathrm{xHFunctionFieldBar}\,M\,H$ and comparison isomorphism $\mathfrak{X}.\mathrm{eeta}$, and let $\Lambda$, $O$ be level data and a `JHNeronObjectAtP` for $p, M, H, Pl$, so that $O$ provides a smooth separated group scheme $O.G \to \mathrm{base}\,p$ with relative group law and a bijection $O.\mathrm{pts}$ from $JH\,M\,H = \mathrm{Pic}^0$ of that function field onto the sections of $O.g$ over $\mathrm{genPt}\,p$. Assume: the designation built from $O.G$, $O.g$ and the unit section represents the relative Picard subfunctor cut out by fibrewise algebraic equivalence to zero, rigidified along $\mathfrak{X}.\varepsilon_{\inf}$, both over $R p$ (`hD`) and after base change to $\mathbb{Q}$ (`hDQ`, with the generic fibre separated); a morphism $\mathrm{ajQ}$ over the base-changed curve into the generic designation, a comparison morphism $k_Q$ between the two pullbacks of the curve (compatible with both projections, the second up to $\mathrm{Spec}$ of $\mathbb{Q} \to \overline{\mathbb{Q}}$), a morphism $\overline{\mathrm{aj}} = \mathfrak{X}.\mathrm{eeta} \ggg k_Q \ggg \mathrm{ajQ} \ggg \mathrm{pr}_1$, a geometric point $\bar\varepsilon$ of $\mathfrak{X}.\mathrm{Meta}.C$ lying over the cusp section, an isomorphism between the generic Poincaré bundle and the base change from $R p$ of the pullback of the integral one, and the Abel–Jacobi pin: for every field $K$, every $t : \mathrm{Spec}\,K \to \mathrm{Spec}\,\mathbb{Q}$ and every $K$-point $x$ of the base-changed curve over $t$, the pullback of the generic Poincaré bundle along $x$ followed by $\mathrm{ajQ}$ is isomorphic to the line bundle of the relative effective Cartier divisor of $x$ tensored with the ideal module of the divisor of the cusp point $t$ followed by the base-changed $\mathfrak{X}.\varepsilon_{\inf}$. Assume further that $O.\mathrm{pts}$ is additive for the group law obtained from `hD`, and that for geometric points $x, s$ of $\mathfrak{X}.\mathrm{Meta}.C$ with $s$ lying over the cusp section there is a degree-zero divisor equal to $[\,\text{place of }x\,] - [\,\text{place of }s\,]$ whose class is sent by $O.\mathrm{pts}$ to $x$ followed by $\overline{\mathrm{aj}}$. Finally let $w_{\mathrm{gen}}$ be a semilinear automorphism of $\mathrm{xHFunctionFieldBar}\,M\,H$ over the algebraic closure of $\mathbb{Q}$ whose action on places is induced by $\mathfrak{X}.\mathrm{w}.\mathrm{hom}$, in the sense that whenever a geometric point $y'$ followed by $\mathfrak{X}.\mathrm{eeta}$, the first projection and $\mathfrak{X}.\mathrm{w}.\mathrm{hom}$ agrees with $y$ followed by $\mathfrak{X}.\mathrm{eeta}$ and the first projection, the place of $y'$ is $w_{\mathrm{gen}}$ applied to the place of $y$. The conclusion: for all $x_1, x_2 \in JH\,M\,H$ and all sections $s_1, s_2, s_1', s_2'$ of $O.g$ over $\Lambda.\sigma_A$ such that $O.\mathrm{pts}(x_i)$ is $\mathrm{barPt}\,Pl$ followed by $s_i$ and $O.\mathrm{pts}(w_{\mathrm{gen}} \cdot x_i)$ is $\mathrm{barPt}\,Pl$ followed by $s_i'$, if $s_1$ and $s_2$ have the same restriction along $\mathrm{resPt}\,Pl$ then so do $s_1'$ and $s_2'$.
--
--   This is the Néron functoriality of the Atkin–Lehner automorphism on the special fibre, in kernel form: on those points of $J_H(M)$ over $\overline{\mathbb{Q}}$ that extend to sections over the valuation ring, the reduction of the Atkin–Lehner translate is determined by the reduction of the point. It is the input used to read the special fibre of an Atkin–Lehner translate through the glued degree-zero divisor class group, in [`ModularCurve.JHNeronObjectAtP.toPic0Pair_ptsSp_symm_section_atkinLehner_fst_eq_zero_iff_snd_eq_zero_of_mem_finPts`](thm.html#ModularCurve.JHNeronObjectAtP.toPic0Pair_ptsSp_symm_section_atkinLehner_fst_eq_zero_iff_snd_eq_zero_of_mem_finPts).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHNeronObjectAtP_resPt_comp_eq_of_resPt_comp_eq_of_pts_smul_atkinLehner_of_abelJacobiPin.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_ModularCurve_JHNeronObjectAtP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped MatrixGroups
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve
  IsLocalRing ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve

set_option maxHeartbeats 800000 in
open ModularCurve in

theorem ModularCurve.JHNeronObjectAtP.resPt_comp_eq_of_resPt_comp_eq_of_pts_smul_atkinLehner_of_abelJacobiPin
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥Pl) p] [IsAlgClosed (IsLocalRing.ResidueField ↥Pl)]
    (hj : ModularCurve.jqModC ℚ ∈ ModularCurve.qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : ModularCurve.XHDRModelAtP p M H hpM hj)
    (Λ : ModularCurve.JHNeronObjectAtP.LevelData p M H hpM Pl)
    (O : ModularCurve.JHNeronObjectAtP p M H hpM Pl hPl Λ)
    (hD : RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) (⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)))
    (hDQ : RepresentsRelSubPic (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (sectionBaseChange ℚ 𝔛.εinf)
        (algEquivZeroCut (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (sectionBaseChange ℚ 𝔛.εinf)) (((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))).baseChange ℚ))
    (hsep : IsSeparated (baseChange (R p) (toBase p (ΓM M H) hj) ℚ))
    (ajQ : SchemeHomOver (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))).baseChange ℚ).toBase)
    (kQ : pullback (toBase p (ΓM M H) hj) (genPt p) ⟶ pullback (toBase p (ΓM M H) hj) (specMap (R p) ℚ))
    (ajbar : 𝔛.Meta.C ⟶ O.G)
    (εbar : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
    (hpoinc : Nonempty (hDQ.poincare.L ≅ (BaseChange.ofR (toBase p (ΓM M H) hj) 𝔛.εinf ℚ
        (hD.poincare.pullbackAlong ⟨pullback.fst O.g (specMap (R p) ℚ), pullback.condition⟩)).L))
    (hajQ : (∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℚ))
        (x : SchemeHomOver t (baseChange (R p) (toBase p (ΓM M H) hj) ℚ)),
        Nonempty ((hDQ.poincare.pullbackAlong
        ⟨x.1 ≫ ajQ.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajQ.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) x.1 x.2).lineBundle ⊗
        (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (t ≫ (sectionBaseChange ℚ 𝔛.εinf).1)
        ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange ℚ 𝔛.εinf).2).trans
        (Category.comp_id t)))).idealModule)))
    (hkQ₁ : kQ ≫ pullback.fst (toBase p (ΓM M H) hj) (specMap (R p) ℚ) = pullback.fst (toBase p (ΓM M H) hj) (genPt p))
    (hkQ₂ : kQ ≫ pullback.snd (toBase p (ΓM M H) hj) (specMap (R p) ℚ) = pullback.snd (toBase p (ΓM M H) hj) (genPt p) ≫ specMap ℚ (AlgebraicClosure ℚ))
    (hajbar : ajbar = 𝔛.eeta ≫ kQ ≫ ajQ.1 ≫ pullback.fst O.g (specMap (R p) ℚ))
    (hεbar : εbar.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1)
    (hpts_law : (∀ x y : JH M H,
        O.pts (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul _ (O.pts x) (O.pts y)))
    (hAJ : (∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
        s.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1 →
        ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)),
        (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
        Finsupp.single (𝔛.Meta.pointEquivPlace x) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace s) 1 ∧
        (O.pts (Pic0.mk Dv)).1 = x.1 ≫ ajbar))
    (wgen : SemilinearAut (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = wgen • 𝔛.Meta.pointEquivPlace y) :
    ∀ (x₁ x₂ : ModularCurve.JH M H) (s₁ s₂ s₁' s₂' : NeronModelInfra.SchemeHomOver Λ.σA O.g),
      (O.pts x₁).1 = barPt Pl ≫ s₁.1 → (O.pts x₂).1 = barPt Pl ≫ s₂.1 →
      (O.pts (wgen • x₁)).1 = barPt Pl ≫ s₁'.1 → (O.pts (wgen • x₂)).1 = barPt Pl ≫ s₂'.1 →
      resPt Pl ≫ s₁.1 = resPt Pl ≫ s₂.1 → resPt Pl ≫ s₁'.1 = resPt Pl ≫ s₂'.1 := by sorry
