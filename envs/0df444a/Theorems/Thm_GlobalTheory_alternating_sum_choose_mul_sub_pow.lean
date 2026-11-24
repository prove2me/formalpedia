-- Prove2me | Theorems.Thm_GlobalTheory_alternating_sum_choose_mul_sub_pow
-- name    : GlobalTheory.alternating_sum_choose_mul_sub_pow
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:03:21.925307+00:00
-- url     : https://prove2.me/theorems/436de31b-6cc2-4062-89d5-e24ac431b562
-- title:
--   Global Theory: alternating sum choose mul sub pow
-- statement:
--   The Global Theory construction uses the alternating sum choose mul sub pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/AlternatingSumChooseMulSubPow.lean#L25-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/AlternatingSumChooseMulSubPow.lean#L25-L52

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_AlternatingSumChooseMulSubPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Finset

theorem GlobalTheory.alternating_sum_choose_mul_sub_pow :
    ∀ g n l : ℕ, g * n ≤ l → ∑ j ∈ Finset.range (g + 1),
      (-1 : ℤ) ^ j * (g.choose j : ℤ) * (((l - j * n) ^ g : ℕ) : ℤ)
        = (g.factorial * n ^ g : ℕ) := by sorry
