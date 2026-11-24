-- Prove2me | Theorems.Thm_GlobalTheory_LevelOfPairing_exists_column
-- name    : GlobalTheory.LevelOfPairing.exists_column
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T18:03:04.238503+00:00
-- url     : https://prove2.me/theorems/db9b453d-afca-4333-bd3f-dccfb6e76e8e
-- title:
--   Level Of Pairing: exists column
-- statement:
--   The Level Of Pairing construction uses the exists column property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/ExistsLevelStructureOfWeilPairing.lean#L50-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/ExistsLevelStructureOfWeilPairing.lean#L50-L65

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_ExistsLevelStructureOfWeilPairing
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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.LevelOfPairing
variable {G U : Type} [Group G] [CommGroup U] {R : G → G → U → Prop} {M : ℕ}

theorem GlobalTheory.LevelOfPairing.exists_column (g : ℕ) (i : Fin (2 * g)) :
    ∃ j : Fin (2 * g), (stdSymp g i j = 1 ∨ stdSymp g i j = -1) ∧ ∀ i', i' ≠ i → stdSymp g i' j = 0 := by sorry
