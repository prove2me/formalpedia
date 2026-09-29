-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_extendsToPlace_pts_smul_sub_of_mem_inertiaSubgroupIn
-- name    : ModularCurve.XHDRModelAtP.extendsToPlace_pts_smul_sub_of_mem_inertiaSubgroupIn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/cbc62be1-69d9-58d7-ae8f-d85ef2183973
-- title:
--   Inertia differences σ x - x extend over the place
-- statement:
--   Fix a prime $p$ and $M \neq 0$ with $p \mid M$ and $p^2 \nmid M$, and a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit whose image in $(\mathbb{Z}/(M/p))^\times$ is $1$; let $hj$ record that the $q$-expansion $j$-series `jqModC ℚ` lies in the function field `qExpFunctionFieldC ℚ ⊤`. Let $\mathfrak{X}$ be a model bundle `XHDRModelAtP p M H hpM hj` for the curve of level $\Gamma_M(M,H)$ over $\mathrm{Spec}\,R_p$, its structure morphism `toBase` assumed proper, and let $D$ be a relative $\mathrm{Pic}^0$ designation over $R_p$ (a scheme $D.P \to \mathrm{Spec}\,R_p$ with a zero section) together with data $hD$, $hD_{\mathbb{Q}}$ exhibiting $D$, respectively its base change to $\mathbb{Q}$, as representing the rigidified line bundles that are fibrewise algebraically trivial relative to the section $\mathfrak{X}.\varepsilon_{\inf}$, the two Poincaré bundles being compatible under base change ($hPQ$). Assume further: an Abel–Jacobi morphism $aj_{\mathbb{Q}}$ over $\mathbb{Q}$ from the curve to $D_{\mathbb{Q}}$ killing the $\varepsilon_{\inf}$-section and classifying, on points over any field, the line bundle of the point tensored with the ideal module of the $\varepsilon_{\inf}$-divisor; a morphism $k_{\mathbb{Q}}$ from the geometric generic fibre to the fibre over $\mathbb{Q}$ compatible with both projections; the induced $\overline{aj}$ on $\mathfrak{X}.\mathrm{Meta}.C$ together with a geometric point $\bar{\varepsilon}$ lying over $\varepsilon_{\inf}$ and sent to the zero section; and a bijection $\mathrm{pts}$ from $J_H(M) = \mathrm{Pic}^0(\overline{\mathbb{Q}}, \mathtt{xHFunctionFieldBar}\,M\,H)$ onto the $\overline{\mathbb{Q}}$-points of $D$ over the generic point, which is additive for the relative group law of $hD$, Galois-equivariant, and computes the class of $[x] - [s]$ as $x$ followed by $\overline{aj}$ whenever $s$ lies over $\varepsilon_{\inf}$. Finally let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $A$, residue field algebraically closed of characteristic $p$, and $\rho : R_p \to A$ compatible with $R_p \to \overline{\mathbb{Q}}$. The conclusion: for every $\sigma$ in the inertia subgroup of $A$ over $\mathbb{Q}$ (the image in $\overline{\mathbb{Q}} \simeq_{\mathbb{Q}} \overline{\mathbb{Q}}$ of the inertia subgroup inside the decomposition subgroup) and every $x \in J_H(M)$, the point $\mathrm{pts}(\sigma \cdot x - x)$ factors as the reduction $\mathrm{Spec}\,\overline{\mathbb{Q}} \to \mathrm{Spec}\,A$ followed by a morphism $\mathrm{Spec}\,A \to D.P$ over $\mathrm{Spec}\,\rho$.
--
--   This is the statement that inertia at $p$ moves every point of $J_H(M)(\overline{\mathbb{Q}})$ by an amount whose image in the relative $\mathrm{Pic}^0$ of the integral model spreads out to an $A$-valued point, the divisorial form of the classical fact that $(\sigma - 1)$ lands in the part of the Jacobian with good specialisation at a place above $p$. It is used, as the inertia clause, in the construction of the level data and dictionary of [`ModularCurve.JHNeronObjectAtP.exists_levelData_representsRelSubPic_dictionary_of_xHDRModelAtP_torusCoords`](thm.html#ModularCurve.JHNeronObjectAtP.exists_levelData_representsRelSubPic_dictionary_of_xHDRModelAtP_torusCoords), en route to level lowering at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_extendsToPlace_pts_smul_sub_of_mem_inertiaSubgroupIn.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
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

theorem ModularCurve.XHDRModelAtP.extendsToPlace_pts_smul_sub_of_mem_inertiaSubgroupIn
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    [IsProper (toBase p (ΓM M H) hj)]
    (D : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))
    (hD : RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) D)

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
        (pts (Pic0.mk Dv)).1 = x.1 ≫ ajbar)

    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)) :
    ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ x : JH M H,
      ExtendsToPlace A (Spec.map (CommRingCat.ofHom ρ)) (pts (σ • x - x)) := by sorry
