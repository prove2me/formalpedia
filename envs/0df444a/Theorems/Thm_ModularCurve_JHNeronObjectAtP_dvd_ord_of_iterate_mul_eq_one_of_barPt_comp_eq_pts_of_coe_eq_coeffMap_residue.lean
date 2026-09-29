-- Prove2me | Theorems.Thm_ModularCurve_JHNeronObjectAtP_dvd_ord_of_iterate_mul_eq_one_of_barPt_comp_eq_pts_of_coe_eq_coeffMap_residue
-- name    : ModularCurve.JHNeronObjectAtP.dvd_ord_of_iterate_mul_eq_one_of_barPt_comp_eq_pts_of_coe_eq_coeffMap_residue
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/fd236b4e-46c5-505d-9b36-6900a326b530
-- title:
--   p-divisibility of the reduced divisor of a p-th root
-- statement:
--   Fix a prime $p$ and $M \ge 1$ with $p \mid M$ and $p^2 \nmid M$, and a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit whose image under `ZMod.unitsMap` along $M/p \mid M$ is trivial. Let $Pl$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a nonunit of $Pl$, whose residue field $\kappa$ is algebraically closed of characteristic $p$, and assume `jqModC ℚ` lies in the $q$-expansion function field of $SL(2,\mathbb{Z})$ over $\mathbb{Q}$. Let $\mathfrak{X}$ be an `XHDRModelAtP` datum for $p, M, H$, let $\Lambda$ be level data and $O$ a `JHNeronObjectAtP` over the base, with structure morphism $O.g$, relative group law $O.L$ and bijection $O.\mathrm{pts} : J_H(M) \to$ sections over the generic geometric point. Further hypotheses, summarised here, assert: the designation formed from $O.G$, $O.g$ and the unit section represents the rigidified relative Picard functor of $\mathfrak{X}$'s curve in the fibrewise algebraically trivial cut, over $R_p$ ($hD$) and after base change to $\mathbb{Q}$ ($hDQ$); separatedness of the generic fibre; an Abel–Jacobi morphism $ajQ$ over $\mathbb{Q}$ sending the section at infinity to the zero section and pulling the Poincaré bundle back to $\mathcal{O}(x-\infty)$ on all field-valued points; a comparison morphism $kQ$ between the two pullbacks of the model; the induced morphism $ajbar$ from the geometric curve model $\mathfrak{X}.\mathrm{Meta}.C$ to $O.G$ together with a base point $\bar\varepsilon$ mapping to the unit section; an isomorphism of the Poincaré bundles over $\mathbb{Q}$ and after base change; additivity of $O.\mathrm{pts}$ for the group law of $hD$; and $hAJ$, which realises $ajbar$ on geometric points by the degree-zero divisor $(x)-(s)$. Let $\rho : R_p \to Pl$ be a ring homomorphism compatible with the structure map to $\overline{\mathbb{Q}}$, let $Dv$ be a degree-zero divisor of $\overline{\mathbb{Q}}$-function field `xHFunctionFieldBar M H`, and let $\sigma$ be a $Pl$-section of $O.g$ over $\operatorname{Spec}\rho$ whose restriction along $\operatorname{Spec}$ of $Pl \hookrightarrow \overline{\mathbb{Q}}$ is the point $O.\mathrm{pts}[Dv]$, and such that the $p$-fold iterate of multiplication by $\sigma$ applied to the unit section is the unit section. Suppose $f \ne 0$ in the function field satisfies $p \cdot Dv(v) = \operatorname{ord}_v f$ for every place $v$, that the Laurent series of $f$ is the image under `coeffMap` of the inclusion $Pl \hookrightarrow \overline{\mathbb{Q}}$ of some $y \in$ `LaurentSeries Pl` whose coefficientwise residue is nonzero, and that $g$ in the $\kappa$-valued $q$-expansion function field at level `ΓN p M H hpM` has Laurent series that coefficientwise residue. Then $p \mid \operatorname{ord}_v g$ for every place $v$ of that field over $\kappa$.
--
--   This is the specialisation step for $p$-torsion classes on the Deligne–Rapoport model: a degree-zero divisor class killed by $p$ after extension to the valuation ring has a $p$-th root function whose reduction along the component of the special fibre through the cusp at infinity again has divisor divisible by $p$. It is used by [`ModularCurve.JHNeronObjectAtP.dvd_ord_of_mem_finPts_of_coe_eq_coeffMap_residue_tauFree`](thm.html#ModularCurve.JHNeronObjectAtP.dvd_ord_of_mem_finPts_of_coe_eq_coeffMap_residue_tauFree) in the analysis of the $p$-torsion of the Jacobian at a prime exactly dividing the level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHNeronObjectAtP_dvd_ord_of_iterate_mul_eq_one_of_barPt_comp_eq_pts_of_coe_eq_coeffMap_residue.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_IharaLemma_IdempotentSplitting
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_ModularCurve_XHHeckeOperator
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_ModularCurve_X1
import Definitions.Def_AlgebraicCurve_GluedPic0Functoriality

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped MatrixGroups
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing AlgebraicCurve
  ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve

set_option maxHeartbeats 800000 in
open ModularCurve in

theorem ModularCurve.JHNeronObjectAtP.dvd_ord_of_iterate_mul_eq_one_of_barPt_comp_eq_pts_of_coe_eq_coeffMap_residue
    (p : ℕ)
    [Fact p.Prime]
    (M : ℕ)
    [NeZero M]
    (hpM : p ∣ M)
    (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (Pl : ValuationSubring (AlgebraicClosure ℚ))
    (hPl : Pl.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥Pl) p]
    [IsAlgClosed (IsLocalRing.ResidueField ↥Pl)]
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
    (hajQε : (sectionBaseChange ℚ 𝔛.εinf).1 ≫ ajQ.1 = (((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))).baseChange ℚ).zeroSection)
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
    (hajbar_over : ajbar ≫ O.g = 𝔛.Meta.toBase ≫ genPt p)
    (hεbar : εbar.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1)
    (hεbar_aj : εbar.1 ≫ ajbar = genPt p ≫ (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1)
    (hpts_law : (∀ x y : JH M H,
        O.pts (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul _ (O.pts x) (O.pts y)))
    (hAJ : (∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
        s.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1 →
        ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)),
        (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
        Finsupp.single (𝔛.Meta.pointEquivPlace x) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace s) 1 ∧
        (O.pts (Pic0.mk Dv)).1 = x.1 ≫ ajbar))

    (ρ : ModularCurve.XHDRLevel.R p →+* ↥Pl)
    (hρ : Pl.subtype.comp ρ = algebraMap (ModularCurve.XHDRLevel.R p) (AlgebraicClosure ℚ))

    (Dv : AlgebraicCurve.Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(ModularCurve.xHFunctionFieldBar M H)))
    (σ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) O.g)
    (hσ : barPt Pl ≫ σ.1 = (O.pts (AlgebraicCurve.Pic0.mk Dv)).1)
    (hpσ : (fun τ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) O.g =>
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul _ τ σ)^[p] ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).one _) =
        (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).one _)

    (f : ↥(ModularCurve.xHFunctionFieldBar M H)) (hf0 : f ≠ 0)
    (hdiv : ∀ v : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H),
      (p : ℤ) * (Dv : AlgebraicCurve.Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H)) v = v.ord f)
    (y : LaurentSeries ↥Pl)
    (hfy : (f : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.coeffMap Pl.subtype y)
    (hy : ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) y ≠ 0)
    (g : ModularCurve.JHNeronObjectAtP.Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl))
    (hg : (g : LaurentSeries (IsLocalRing.ResidueField ↥Pl)) = ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) y) :
    ∀ v : AlgebraicCurve.Place (IsLocalRing.ResidueField ↥Pl) (ModularCurve.JHNeronObjectAtP.Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl)),
      (p : ℤ) ∣ v.ord g := by sorry
