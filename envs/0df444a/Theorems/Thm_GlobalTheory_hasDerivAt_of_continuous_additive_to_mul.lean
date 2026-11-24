-- Prove2me | Theorems.Thm_GlobalTheory_hasDerivAt_of_continuous_additive_to_mul
-- name    : GlobalTheory.hasDerivAt_of_continuous_additive_to_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:49:57.049872+00:00
-- url     : https://prove2.me/theorems/6eece6bd-75be-44f2-bf02-a772ae3674d9
-- title:
--   Global Theory: has Deriv At of continuous additive to mul
-- statement:
--   The Global Theory construction uses the has Deriv At of continuous additive to mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasDerivAtOfContinuousRealToComplexExponential.lean#L7-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasDerivAtOfContinuousRealToComplexExponential.lean#L7-L16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasDerivAtOfContinuousOfMapAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasDerivAtOfContinuousRealToComplexExponential
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
open GlobalTheory

theorem GlobalTheory.hasDerivAt_of_continuous_additive_to_mul (χ : ℝ → ℂ) (hc : Continuous χ)
    (hmul : ∀ s t, χ (s + t) = χ s * χ t) (h0 : χ 0 = 1) :
    ∀ s, HasDerivAt χ (deriv χ 0 * χ s) s := by sorry
