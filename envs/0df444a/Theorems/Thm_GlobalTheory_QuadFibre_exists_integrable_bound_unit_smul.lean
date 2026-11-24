-- Prove2me | Theorems.Thm_GlobalTheory_QuadFibre_exists_integrable_bound_unit_smul
-- name    : GlobalTheory.QuadFibre.exists_integrable_bound_unit_smul
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T19:10:08.611536+00:00
-- url     : https://prove2.me/theorems/360359b3-06d4-4bb2-a1fb-74fa9b943c2c
-- title:
--   Quad Fibre: exists integrable bound unit smul
-- statement:
--   The Quad Fibre construction uses the exists integrable bound unit smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/IntegrableContinuousOnAveragedFibreIntegral.lean#L54-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/IntegrableContinuousOnAveragedFibreIntegral.lean#L54-L81

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_FibOfZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IntegrableContinuousOnAveragedFibreIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
open scoped Pointwise
open GlobalTheory GlobalTheory.QuadFibre

theorem GlobalTheory.QuadFibre.exists_integrable_bound_unit_smul {K V : Type} [NormedField K] [ProperSpace K]
    [AddCommGroup V] [Module K V] [TopologicalSpace V] [ContinuousSMul K V] [T2Space V]
    [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [IsFiniteMeasureOnCompacts μ]
    {φ : V → ℝ} (hφ : Continuous φ) (hc : HasCompactSupport φ) :
    ∃ g : V → ℝ, Integrable g μ ∧ ∀ (a : K) (x : V), ‖a‖ = 1 → ‖φ (a • x)‖ ≤ g x := by sorry
