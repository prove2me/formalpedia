-- Prove2me | Theorems.Thm_GlobalTheory_hasSum_of_dominated_of_eq_near_zero
-- name    : GlobalTheory.hasSum_of_dominated_of_eq_near_zero
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:54:25.111953+00:00
-- url     : https://prove2.me/theorems/90e90a08-9155-4dbc-9ec1-70631d1ddc67
-- title:
--   Global Theory: has Sum of dominated of eq near zero
-- statement:
--   The Global Theory construction uses the has Sum of dominated of eq near zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HasSumOfDominatedOfEqNearZero.lean#L7-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HasSumOfDominatedOfEqNearZero.lean#L7-L51

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasSumOfDominatedOfEqNearZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Metric Filter Topology
open GlobalTheory

theorem GlobalTheory.hasSum_of_dominated_of_eq_near_zero {ι : Type} (b : ι → ℂ) (c : ι → ℝ) (n : ι → ℕ)
    (R : ℂ → ℂ) (r ε : ℝ)
    (hbc : ∀ i, ‖b i‖ ≤ c i)
    (hc : ∀ x : ℝ, 0 ≤ x → x < r → Summable (fun i => c i * x ^ n i)) (hε : 0 < ε)
    (hR : DifferentiableOn ℂ R (Metric.ball 0 r))
    (hnear : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < ε → HasSum (fun i => b i * z ^ n i) (R z)) :
    ∀ z : ℂ, ‖z‖ < r → HasSum (fun i => b i * z ^ n i) (R z) := by sorry
