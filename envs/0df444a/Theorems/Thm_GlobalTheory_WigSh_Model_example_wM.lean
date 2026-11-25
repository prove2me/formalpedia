-- Prove2me | Theorems.Thm_GlobalTheory_WigSh_Model_example_wM
-- name    : GlobalTheory.WigSh.Model.example_wM
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:43:48.922204+00:00
-- url     : https://prove2.me/theorems/95e9b318-b33b-4288-b298-31fb9b8915e0
-- title:
--   Model: example w M
-- statement:
--   The Model construction uses the example w M property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Jets/FactorNonneg.lean#L107-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Jets/FactorNonneg.lean#L107-L112

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

theorem GlobalTheory.WigSh.Model.example_wM : wM ![3, -1] ![1] 0 = 1 / 2 ∧ wM ![3, -1] ![1] 1 = 1 / 2 := by sorry
