-- Prove2me | Theorems.Thm_GlobalTheory_summable_nonneg_family_of_differentiableOn
-- name    : GlobalTheory.summable_nonneg_family_of_differentiableOn
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:22:30.398125+00:00
-- url     : https://prove2.me/theorems/006ddf95-39ca-46cd-857a-13bd9fea0a2b
-- title:
--   Global Theory: summable nonneg family of differentiable On
-- statement:
--   The Global Theory construction uses the summable nonneg family of differentiable On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SummableNonnegFamilyOfDifferentiableOn.lean#L7-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SummableNonnegFamilyOfDifferentiableOn.lean#L7-L105

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SummableNonnegFamilyOfDifferentiableOn
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory

theorem GlobalTheory.summable_nonneg_family_of_differentiableOn {ι : Type} (c : ι → ℝ) (n : ι → ℕ)
    (R : ℂ → ℂ) (r ε : ℝ) (hc : ∀ i, 0 ≤ c i) (hε : 0 < ε)
    (hR : DifferentiableOn ℂ R (Metric.ball 0 r))
    (hser : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < ε → HasSum (fun i => (c i : ℂ) * z ^ n i) (R z))
    (x : ℝ) (hx0 : 0 ≤ x) (hxr : x < r) : Summable (fun i => c i * x ^ n i) := by sorry
