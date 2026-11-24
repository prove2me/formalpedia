-- Prove2me | Theorems.Thm_GlobalTheory_CMType_trace_eq_sum_two_mul_re
-- name    : GlobalTheory.CMType.trace_eq_sum_two_mul_re
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T11:04:16.352094+00:00
-- url     : https://prove2.me/theorems/65ce2d57-2e72-4c7f-baab-cea6f4a7030e
-- title:
--   CMType: trace eq sum two mul re
-- statement:
--   The CMType construction uses the trace eq sum two mul re property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/MemIffConjugateNotMem.lean#L108-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/MemIffConjugateNotMem.lean#L108-L117

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_MemIffConjugateNotMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped ComplexConjugate
open GlobalTheory
open GlobalTheory.CMType
variable {E : Type*} [Field E] [NumberField E] (Φ : CMType E)

theorem GlobalTheory.CMType.trace_eq_sum_two_mul_re (x : E) :
    ((Algebra.trace ℚ E x : ℚ) : ℝ) = ∑ τ : Φ, 2 * (τ.1 x).re := by sorry
