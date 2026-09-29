-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_exists_section_comp_snd_eq_barPt_comp_eq_pointEquivPlace_symm
-- name    : ModularCurve.XHDRModelAtP.exists_section_comp_snd_eq_barPt_comp_eq_pointEquivPlace_symm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/2cd3f12b-61e0-5551-9728-46fda85a2d98
-- title:
--   Places give A-valued sections of the base-changed model
-- statement:
--   Fix a prime $p$ and a modulus $M$ with $p \mid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$, hypotheses $\neg\,p^2 \mid M$ and that every unit of $\mathbb{Z}/M$ mapping to $1$ in $(\mathbb{Z}/(M/p))^\times$ lies in $H$, together with the hypothesis `hj` that the $q$-expansion $j$-series $\mathrm{jqModC}\ \mathbb{Q}$ belongs to the $q$-expansion function field of the full level, and let $\mathfrak{X}$ be an `XHDRModelAtP p M H hpM hj` package; in particular $\mathfrak{X}$ provides properness of `toBase p (ΓM M H) hj` over the base ring $R_p$, a curve model $\mathfrak{X}.\mathrm{Meta}$ over $\overline{\mathbb{Q}}$ with function field $\mathrm{xHFunctionFieldBar}\ M\ H$, and an isomorphism $\mathfrak{X}.\mathrm{eeta}$ from $\mathfrak{X}.\mathrm{Meta}.C$ onto the pullback of `toBase` along $\operatorname{Spec}$ of $R_p \to \overline{\mathbb{Q}}$ compatible with the structure morphisms. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$, let $O$ be a commutative ring with a ring map $\rho_O : R_p \to O$, let $j_O : O \to \overline{\mathbb{Q}}$ satisfy $j_O \circ \rho_O =$ the structure map $R_p \to \overline{\mathbb{Q}}$, let $\iota_A : O \to A$ satisfy $A \hookrightarrow \overline{\mathbb{Q}}$ composed after $\iota_A$ equal to $j_O$, and let $W$ be a place of $\mathrm{xHFunctionFieldBar}\ M\ H$ over $\overline{\mathbb{Q}}$. Then there is a morphism $s_A : \operatorname{Spec} A \to \mathrm{XO}\ (ΓM\ M\ H)\ hj\ \rho_O$, the pullback of `toBase` along $\operatorname{Spec}\rho_O$, such that $s_A$ followed by the second projection is $\operatorname{Spec} \iota_A$, and such that $\operatorname{Spec}$ of the inclusion $A \hookrightarrow \overline{\mathbb{Q}}$ followed by $s_A$ equals the $\overline{\mathbb{Q}}$-point of $\mathfrak{X}.\mathrm{Meta}.C$ attached to $W$ by the inverse of `pointEquivPlace`, followed by $\mathfrak{X}.\mathrm{eeta}$ and then by the canonical map of pullbacks induced by the identity on the model and by $\operatorname{Spec} j_O$ on bases.
--
--   This is the valuative criterion of properness applied to the Deligne–Rapoport-style model of $X_H(M)$ at a prime $p$ exactly dividing $M$: any place of the geometric function field, viewed as a $\overline{\mathbb{Q}}$-point of the geometric fibre, extends to a section over the valuation ring $A$ of the model base-changed along $\rho_O : R_p \to O$. It feeds the analysis of sections meeting the crossings of the special fibre, being cited by [`ModularCurve.XHDRModelAtP.exists_section_through_crossing_iff_reduceFst_eq_and_not_isStrict_of_offDiag_of_surjective`](thm.html#ModularCurve.XHDRModelAtP.exists_section_through_crossing_iff_reduceFst_eq_and_not_isStrict_of_offDiag_of_surjective).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_exists_section_comp_snd_eq_barPt_comp_eq_pointEquivPlace_symm.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_ComponentGroup
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_ModularCurve_XHDRModelAtPCrossingFrame
import Definitions.Def_AlgebraicCurve_PlaceEvaluation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve
  IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP
open scoped MatrixGroups

theorem ModularCurve.XHDRModelAtP.exists_section_comp_snd_eq_barPt_comp_eq_pointEquivPlace_symm
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ))

    (O : Type) [CommRing O] (ρO : R p →+* O)
    (jO : O →+* AlgebraicClosure ℚ) (hjO : jO.comp ρO = algebraMap (R p) (AlgebraicClosure ℚ))
    (ιA : O →+* ↥A) (hιA : A.subtype.comp ιA = jO)
    (W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) :
    ∃ sA : Spec (CommRingCat.of ↥A) ⟶ XO (ΓM M H) hj ρO,
      sA ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom ιA) ∧
      barPt A ≫ sA = ((𝔛.Meta).pointEquivPlace.symm W).1 ≫ 𝔛.eeta ≫
        (pullback.map (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))
          (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρO)) (𝟙 _) (Spec.map (CommRingCat.ofHom jO)) (𝟙 _)
          (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hjO]) :
          pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) ⟶ XO (ΓM M H) hj ρO) := by sorry
