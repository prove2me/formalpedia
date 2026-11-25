-- Prove2me | Theorems.Thm_GlobalTheory_LowCasShift_nsq_sub_single
-- name    : GlobalTheory.LowCasShift.nsq_sub_single
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:59:46.12385+00:00
-- url     : https://prove2.me/theorems/ae7819a7-a234-48e1-bd64-416173dc041a
-- title:
--   Low Cas Shift: nsq sub single
-- statement:
--   The Low Cas Shift construction uses the nsq sub single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/LowKSubSingleSqrtCkvLe.lean#L29-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/LowKSubSingleSqrtCkvLe.lean#L29-L39

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_SumIoPr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_LowKSubSingleSqrtCkvLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace
open GlobalTheory GlobalTheory.LowCasShift

theorem GlobalTheory.LowCasShift.nsq_sub_single {n : ℕ} (u : Fin n → ℝ) (s : Fin n) :
    nsq (u - Pi.single s 1) = nsq u - 2 * u s + 1 := by sorry
