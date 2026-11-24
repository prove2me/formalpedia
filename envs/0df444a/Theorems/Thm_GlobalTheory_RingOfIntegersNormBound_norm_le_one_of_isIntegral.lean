-- Prove2me | Theorems.Thm_GlobalTheory_RingOfIntegersNormBound_norm_le_one_of_isIntegral
-- name    : GlobalTheory.RingOfIntegersNormBound.norm_le_one_of_isIntegral
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:18:39.904346+00:00
-- url     : https://prove2.me/theorems/bddaef81-e62e-4539-a070-2f723be43673
-- title:
--   Ring Of Integers Norm Bound: norm le one of is Integral
-- statement:
--   The Ring Of Integers Norm Bound construction uses the norm le one of is Integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormMapRingOfIntegersLeOne.lean#L5-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormMapRingOfIntegersLeOne.lean#L5-L35

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

theorem GlobalTheory.RingOfIntegersNormBound.norm_le_one_of_isIntegral {F : Type*} [NormedField F] [IsUltrametricDist F]
    {x : F} (hx : IsIntegral ℤ x) : ‖x‖ ≤ 1 := by sorry
