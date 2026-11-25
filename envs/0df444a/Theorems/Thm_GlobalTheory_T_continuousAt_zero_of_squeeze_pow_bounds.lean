-- Prove2me | Theorems.Thm_GlobalTheory_T_continuousAt_zero_of_squeeze_pow_bounds
-- name    : GlobalTheory.T.continuousAt_zero_of_squeeze_pow_bounds
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:39:09.422937+00:00
-- url     : https://prove2.me/theorems/74683da7-7734-5ca0-9240-c984383763b7
-- title:
--   T: continuous At zero of squeeze pow bounds
-- statement:
--   The T construction uses the continuous At zero of squeeze pow bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ContinuousAtZeroOfSqueezePowBoundsStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ContinuousAtZeroOfSqueezePowBoundsStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ContinuousAtZeroOfSqueezePowBounds
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_UpperDens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ContinuousAtZeroOfSqueezePowBoundsStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped ENNReal NNReal
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.continuousAt_zero_of_squeeze_pow_bounds : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (d : ℕ) (f : V → ℝ≥0∞) (c : ℝ≥0∞), c ≠ ⊤ → (∀ ε : ℝ, 0 < ε → ε < 1 → ∃ η : ℝ, 0 < η ∧ ∀ x : V, ‖x‖ < η → ENNReal.ofReal ((1 + ε)⁻¹ ^ d) * c ≤ f x ∧ f x ≤ ENNReal.ofReal (((1 + ε) / (1 - ε)) ^ d) * c) → f 0 = c ∧ ContinuousAt f 0 := by sorry
