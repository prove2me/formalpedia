-- Prove2me | Theorems.Thm_GlobalTheory_exists_nat_trace_of_pow_four
-- name    : GlobalTheory.exists_nat_trace_of_pow_four
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:36:33.337823+00:00
-- url     : https://prove2.me/theorems/fbce8ed8-53ca-40cb-bf44-8249450a4263
-- title:
--   Global Theory: exists nat trace of pow four
-- statement:
--   The Global Theory construction uses the exists nat trace of pow four property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsRepresentativesQuotientRangeMulVecLin.lean#L17-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsRepresentativesQuotientRangeMulVecLin.lean#L17-L33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRepresentativesQuotientRangeMulVecLin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Matrix
open GlobalTheory
variable {A : Type*} [Fintype A] [DecidableEq A]

theorem GlobalTheory.exists_nat_trace_of_pow_four {V : Matrix A A ℂ} (hV : V ^ 4 = 1) :
    ∃ r : ℕ, (Fintype.card A : ℂ) + V.trace + (V ^ 2).trace + (V ^ 3).trace = 4 * r := by sorry
