-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_AxForm_exists_split
-- name    : GlobalTheory.CompanionTheory.AxForm.exists_split
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:23:28.561518+00:00
-- url     : https://prove2.me/theorems/a969656f-0104-495c-960e-ac23c250b072
-- title:
--   Ax Form: exists split
-- statement:
--   The Ax Form construction uses the exists split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ModuleHomCompSquareZeroSection.lean#L249-L305
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ModuleHomCompSquareZeroSection.lean#L249-L305

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbelianSchemeGerms
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ModuleHomCompSquareZeroSection
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open KaehlerDifferential
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AxForm
variable {R : Type} [CommRing R]
variable {B M : Type} [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M]
  [IsCentralScalar B M]

theorem GlobalTheory.CompanionTheory.AxForm.exists_split (A : Over (Sp R)) [GrpObj A] (y : TT (r1 R B M) ⟶ A ⊗ A)
    (hy : pt (ρ := r1 R B M) (TrivSqZeroExt.fstHom B B M).toRingHom fst_comp_square_zero_section ≫ y = lift (x0 A B) (x0 A B)) :
    ∃ Y : TT (r1 R B (M × M)) ⟶ A ⊗ A,
      pt (ρ := r1 R B (M × M)) (TrivSqZeroExt.fstHom B B (M × M)).toRingHom fst_comp_square_zero_section ≫ Y = lift (x0 A B) (x0 A B) ∧
      pt (mH (LinearMap.fst B M M + LinearMap.snd B M M)) (module_hom_comp_square_zero_section _) ≫ Y = y ∧
      pt (mH (LinearMap.fst B M M)) (module_hom_comp_square_zero_section _) ≫ Y =
        (y ≫ CartesianMonoidalCategory.fst A A) ≫ lift (𝟙 A) (1 : A ⟶ A) ∧
      pt (mH (LinearMap.snd B M M)) (module_hom_comp_square_zero_section _) ≫ Y =
        (y ≫ CartesianMonoidalCategory.snd A A) ≫ lift (1 : A ⟶ A) (𝟙 A) := by sorry
