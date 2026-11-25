-- Prove2me | Theorems.Thm_GlobalTheory_WigSh_Model_Box_strictAnti
-- name    : GlobalTheory.WigSh.Model.Box.strictAnti
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:53:31.479632+00:00
-- url     : https://prove2.me/theorems/7f51d647-92a2-5268-b537-87913c8366cd
-- title:
--   Box: strict Anti
-- statement:
--   The Box construction uses the strict Anti property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Jets/FactorNonneg.lean#L13-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Jets/FactorNonneg.lean#L13-L17

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

theorem GlobalTheory.WigSh.Model.Box.strictAnti {n : ℕ} {L : Fin (n + 1) → ℤ} {M : Fin n → ℤ} (h : Box L M) :
    StrictAnti L := by sorry
