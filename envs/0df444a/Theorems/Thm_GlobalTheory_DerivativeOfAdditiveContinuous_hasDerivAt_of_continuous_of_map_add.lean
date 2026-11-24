-- Prove2me | Theorems.Thm_GlobalTheory_DerivativeOfAdditiveContinuous_hasDerivAt_of_continuous_of_map_add
-- name    : GlobalTheory.DerivativeOfAdditiveContinuous.hasDerivAt_of_continuous_of_map_add
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T12:43:34.337805+00:00
-- url     : https://prove2.me/theorems/c5451c60-0d4f-4a5a-9881-c011738f55b6
-- title:
--   Derivative Of Additive Continuous: has Deriv At of continuous of map add
-- statement:
--   The Derivative Of Additive Continuous construction uses the has Deriv At of continuous of map add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasDerivAtOfContinuousOfMapAdd.lean#L5-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasDerivAtOfContinuousOfMapAdd.lean#L5-L66

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasDerivAtOfContinuousOfMapAdd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DerivativeOfAdditiveContinuous

theorem GlobalTheory.DerivativeOfAdditiveContinuous.hasDerivAt_of_continuous_of_map_add (χ : ℝ → ℂ) (hc : Continuous χ)
    (hadd : ∀ s t : ℝ, χ (s + t) = χ s * χ t) (h0 : χ (0 : ℝ) = (1 : ℂ)) (s : ℝ) :
    HasDerivAt χ (deriv χ (0 : ℝ) * χ s) s := by sorry
