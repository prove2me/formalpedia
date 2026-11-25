-- Prove2me | Theorems.Thm_GlobalTheory_Mem_Chr_Model_diagUnits_neg_one_ne
-- name    : GlobalTheory.Mem.Chr.Model.diagUnits_neg_one_ne
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:14:23.506341+00:00
-- url     : https://prove2.me/theorems/53e08d7c-1113-4543-bf79-cc1bc7e16350
-- title:
--   Model: diag Units neg one ne
-- statement:
--   The Model construction uses the diag Units neg one ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/DiagUnitsEqLocalIdele.lean#L111-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/DiagUnitsEqLocalIdele.lean#L111-L117

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_ValuedAlgebraMapEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_DiagUnitsEqLocalIdele
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Chr.Model
variable (L : Type) [Field L] [NumberField L]

theorem GlobalTheory.Mem.Chr.Model.diagUnits_neg_one_ne : diagUnits L (-1) ≠ 1 := by sorry
