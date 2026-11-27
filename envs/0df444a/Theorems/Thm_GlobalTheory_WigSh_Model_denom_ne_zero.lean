-- Prove2me | Theorems.Thm_GlobalTheory_WigSh_Model_denom_ne_zero
-- name    : GlobalTheory.WigSh.Model.denom_ne_zero
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:43:23.425899+00:00
-- url     : https://prove2.me/theorems/5cd1bb24-9a5e-576b-bb23-baadc4874dad
-- title:
--   Model: denom ne zero
-- statement:
--   The Model construction uses the denom ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Jets/FactorNonneg.lean#L59-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Jets/FactorNonneg.lean#L59-L63

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_Imports
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_FactorNonneg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open GlobalTheory GlobalTheory.WigSh GlobalTheory.WigSh.Model

theorem GlobalTheory.WigSh.Model.denom_ne_zero {n : ℕ} {L : Fin (n + 1) → ℤ} {M : Fin n → ℤ} (h : Box L M)
    (l : Fin (n + 1)) : ∏ j ∈ univ.erase l, ((L j : ℝ) - (L l : ℝ)) ≠ 0 := by sorry
