-- Prove2me | Theorems.Thm_GlobalTheory_PowerExtensionEvaluation_pow_le_comap_map_pow
-- name    : GlobalTheory.PowerExtensionEvaluation.pow_le_comap_map_pow
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T18:52:51.079012+00:00
-- url     : https://prove2.me/theorems/71d999a6-3aa9-48ef-aa85-22b93c6017f0
-- title:
--   Power Extension Evaluation: pow le comap map pow
-- statement:
--   The Power Extension Evaluation construction uses the pow le comap map pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/PowLeComapMapPow.lean#L7-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/PowLeComapMapPow.lean#L7-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_PowLeComapMapPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2
open GlobalTheory GlobalTheory.PowerExtensionEvaluation

theorem GlobalTheory.PowerExtensionEvaluation.pow_le_comap_map_pow {A : Type u_1} {B : Type u_2} [CommRing A] [CommRing B]
    (I : Ideal A) (f : A →+* B) (n : ℕ) : I ^ n ≤ ((I.map f) ^ n).comap f := by sorry
