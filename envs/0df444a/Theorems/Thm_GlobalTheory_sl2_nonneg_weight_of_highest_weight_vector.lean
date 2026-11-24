-- Prove2me | Theorems.Thm_GlobalTheory_sl2_nonneg_weight_of_highest_weight_vector
-- name    : GlobalTheory.sl2_nonneg_weight_of_highest_weight_vector
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:20:51.170699+00:00
-- url     : https://prove2.me/theorems/7086422c-b515-45b6-967b-10b09d760e86
-- title:
--   Global Theory: sl2 nonneg weight of highest weight vector
-- statement:
--   The Global Theory construction uses the sl2 nonneg weight of highest weight vector property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/Sl2NonnegWeightOfHighestWeightVector.lean#L52-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/Sl2NonnegWeightOfHighestWeightVector.lean#L52-L127

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_Sl2NonnegWeightOfHighestWeightVector
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.sl2_nonneg_weight_of_highest_weight_vector {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]
    (E F H : Module.End K V) (hEF : E * F - F * E = H) (hHF : H * F - F * H = -(F + F))
    (W : Submodule K V) [FiniteDimensional K W] (hW : ∀ w ∈ W, F w ∈ W)
    (v : V) (hvW : v ∈ W) (hv0 : v ≠ 0) (l : ℤ) (hE : E v = 0) (hH : H v = (l : K) • v) : 0 ≤ l := by sorry
