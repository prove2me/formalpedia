-- Prove2me | Theorems.Thm_GlobalTheory_T_haar_measure_pi_change_constant
-- name    : GlobalTheory.T.haar_measure_pi_change_constant
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T20:42:01.478801+00:00
-- url     : https://prove2.me/theorems/8b392b4a-82d0-4ae5-af12-1a103d22b1c4
-- title:
--   T: haar measure pi change constant
-- statement:
--   The T construction uses the haar measure pi change constant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HaarMeasurePiChangeConstantStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HaarMeasurePiChangeConstantStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HaarMeasurePiChangeConstant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NabsDetEqOfActEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HaarMeasurePiChangeConstantStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.HalfPowerSpherical
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.haar_measure_pi_change_constant : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ι : Type) [Fintype ι] (ν νs : Measure k) (d : ι → kˣ), ν.IsAddHaarMeasure → νs.IsAddHaarMeasure → ∃ C : ℝ, (0 < C ∧ (IsHalfPow k (ν (𝒪[k] : Set k)).toReal → IsHalfPow k (νs (𝒪[k] : Set k)).toReal → IsHalfPow k C)) ∧ ∀ F : (ι → k) → ℂ, ∫ e, F e ∂(Measure.pi fun _ => ν) = C * ∫ e, F (fun i => (d i : k) * e i) ∂(Measure.pi fun _ => νs) := by sorry
