-- Prove2me | Theorems.Thm_GlobalTheory_Mem_An_Model_not_normOne
-- name    : GlobalTheory.Mem.An.Model.not_normOne
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:14:17.939344+00:00
-- url     : https://prove2.me/theorems/b5e0a8da-633a-46d8-a689-342236762eb8
-- title:
--   Model: not norm One
-- statement:
--   The Model construction uses the not norm One property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/NormOneSevenOneTwo.lean#L26-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/NormOneSevenOneTwo.lean#L26-L33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_RayPrimes
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_NormOneSevenOneTwo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset ArithmeticFunction NumberField IsDedekindDomain
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.An GlobalTheory.Mem.An.Model

theorem GlobalTheory.Mem.An.Model.not_normOne : ¬ NormOne 7 2 2 := by sorry
