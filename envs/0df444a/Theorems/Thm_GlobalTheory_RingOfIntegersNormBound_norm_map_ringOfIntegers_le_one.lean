-- Prove2me | Theorems.Thm_GlobalTheory_RingOfIntegersNormBound_norm_map_ringOfIntegers_le_one
-- name    : GlobalTheory.RingOfIntegersNormBound.norm_map_ringOfIntegers_le_one
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:20:05.019065+00:00
-- url     : https://prove2.me/theorems/0efaec1e-5f20-45b5-ad7e-8783441413e9
-- title:
--   Ring Of Integers Norm Bound: norm map ring Of Integers le one
-- statement:
--   The Ring Of Integers Norm Bound construction uses the norm map ring Of Integers le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormMapRingOfIntegersLeOne.lean#L37-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormMapRingOfIntegersLeOne.lean#L37-L40

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormMapRingOfIntegersLeOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.RingOfIntegersNormBound

theorem GlobalTheory.RingOfIntegersNormBound.norm_map_ringOfIntegers_le_one {K : Type} [Field K] [NumberField K] {p : ℕ}
    [Fact (Nat.Prime p)] (f : K →+* ℂ_[p]) (c : NumberField.RingOfIntegers K) :
    ‖(f : K → ℂ_[p]) (↑c : K)‖ ≤ (1 : ℝ) := by sorry
