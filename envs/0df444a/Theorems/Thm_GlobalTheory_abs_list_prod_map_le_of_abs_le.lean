-- Prove2me | Theorems.Thm_GlobalTheory_abs_list_prod_map_le_of_abs_le
-- name    : GlobalTheory.abs_list_prod_map_le_of_abs_le
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:34:43.627142+00:00
-- url     : https://prove2.me/theorems/2bff744e-1ed0-40dc-a7a1-2e20f1e93940
-- title:
--   Global Theory: abs list prod map le of abs le
-- statement:
--   The Global Theory construction uses the abs list prod map le of abs le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/GramBlockDiagonalEnergyBound.lean#L7-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/GramBlockDiagonalEnergyBound.lean#L7-L15

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_GramBlockDiagonalEnergyBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Finset
open GlobalTheory

theorem GlobalTheory.abs_list_prod_map_le_of_abs_le {α : Type} (L : List α) (f n : α → ℝ)
    (h : ∀ a ∈ L, |f a| ≤ n a) : |(L.map f).prod| ≤ (L.map n).prod := by sorry
