-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_cover_model_irreducible_specialFibre
-- name    : GlobalTheory.T.exists_cover_model_irreducible_specialFibre
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T20:34:16.817552+00:00
-- url     : https://prove2.me/theorems/2ce2aa9d-3b38-44e5-bdf4-48b245f79d68
-- title:
--   T: exists cover model irreducible special Fibre
-- statement:
--   The T construction uses the exists cover model irreducible special Fibre property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsCoverModelIrreducibleSpecialFibreStatement.lean#L13-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsCoverModelIrreducibleSpecialFibreStatement.lean#L13-L14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsCoverModelIrreducibleSpecialFibre
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsCoverModelIrreducibleSpecialFibreStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_cover_model_irreducible_specialFibre : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (A : Over (Sp K)) (M : Model R A), ∃ (n : ℕ) (N : Fin n → Model R A) (g : ∀ i, (N i).Y ⟶ M.Y), (∀ i, (N i).Irr ∧ IsOpenImmersion (g i).left ∧ (N i).j ≫ (g i).left = M.j) ∧ ∀ y ∈ M.sp, ∃ i, y ∈ Set.range (g i).left := by sorry
