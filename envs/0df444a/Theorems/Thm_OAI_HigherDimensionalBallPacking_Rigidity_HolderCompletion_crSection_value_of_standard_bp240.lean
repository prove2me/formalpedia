-- Prove2me | Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_crSection_value_of_standard_bp240
-- name    : OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.crSection_value_of_standard_bp240
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T01:52:20.855934+00:00
-- url     : https://prove2.me/theorems/c7ccaefc-6499-4b93-8963-86c79a252e30
-- title:
--   OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.crSection_value_of_standard_bp240: intermediate lemma from OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.crSection_value_of_standard` of [lean/OAI/Geometry/BallPacking/Fredholm/PointwiseMarkedCR.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Fredholm/PointwiseMarkedCR.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion`, with `open scoped ContDiff Topology BoundedContinuousFunction`, `open Set Function Filter`):
--
--   ```lean
--   lemma crSection_value_of_standard_bp240 [CompleteSpace E] (w : COne ℂ E) (z : ℂ)
--       (hz : J (affineCurve p (complexSlope a) w z)=complexI (E := E)) :
--       valueCLM _ (crSection hJ p (complexSlope a) w) z = valueCLM _ (standardJetCR w) z
--   ```
--
--   **Definitions.** The statement is written with `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.Ambient`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.BoundedCThree`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.COne`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.HMap`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.Holder`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.JetAmbient`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.Pairs` and `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.valueCLM` (definitions bundle `OAIQ240Bp000` of this split); `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.complexI`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.complexSlope`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeChartInst1` and `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeChartInst2` (definitions bundle `OAIQ240Bp001` of this split); `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.standardJetCR` (definitions bundle `OAIQ240Bp023` of this split); `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.affineCurve` (definitions bundle `OAIQ240Bp024` of this split); `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.crSection` (definitions bundle `OAIQ240Bp025` of this split).
--
--   **Used by.** The proofs of `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actualFreeChart_crSection_fderiv_eval_bp240` and `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.regularityTranslation_smooth_bp240` of this split import it.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Fredholm/PointwiseMarkedCR.lean (declaration OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.crSection_value_of_standard)

import Mathlib
import Definitions.Def_OAIQ240Bp025

section

attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion

open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeChartInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeChartInst2
local instance freeChartInst3_r0c9cee_1 : NormedAddCommGroup (COne ℂ E) := inferInstance
local instance freeChartInst4_r0c9cee_1 : NormedSpace ℝ (COne ℂ E) := inferInstance
local instance freeChartInst5_r0c9cee_1 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance freeChartInst6_r0c9cee_1 : NormedSpace ℝ (HMap ℂ E) := inferInstance
variable {J : E → E →L[ℝ] E} (hJ : BoundedCThree J) (b : ContDiffBump (0:ℂ)) (p a : E)
variable (u : freeModel (E := E) (Metric.closedBall (0:ℂ) b.rOut))

local instance freeChartInst7_r0c9cee_1 : NormedAddCommGroup (freeModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance freeChartInst8_r0c9cee_1 : NormedSpace ℝ (freeModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance freeChartInst9_r0c9cee_1 : NormedAddCommGroup (supportedHolder (E := E) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance freeChartInst10_r0c9cee_1 : NormedSpace ℝ (supportedHolder (E := E) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
omit [CompleteSpace E] in
lemma crSection_value_of_standard_bp240 [CompleteSpace E] (w : COne ℂ E) (z : ℂ)
    (hz : J (affineCurve p (complexSlope a) w z)=complexI (E := E)) :
    valueCLM _ (crSection hJ p (complexSlope a) w) z = valueCLM _ (standardJetCR w) z := by
  sorry

end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end
