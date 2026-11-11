-- Prove2me | Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_freeTranslation_zero_bp240
-- name    : OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeTranslation_zero_bp240
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T01:10:57.140931+00:00
-- url     : https://prove2.me/theorems/9482527e-01e6-4b8f-b332-a1dc74c5b259
-- title:
--   OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeTranslation_zero_bp240: intermediate lemma from OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeTranslation_zero` of [lean/OAI/Geometry/BallPacking/Fredholm/FreeLinearization.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Fredholm/FreeLinearization.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion`, with `open scoped ContDiff Topology BoundedContinuousFunction`, `open Set Function Filter`):
--
--   ```lean
--   @[simp] lemma freeTranslation_zero_bp240 : freeTranslation hRS a u 0=0
--   ```
--
--   **Definitions.** The statement is written with `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.Ambient`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.COne`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.Holder`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.JetAmbient` and `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.Pairs` (definitions bundle `OAIQ240Bp000` of this split); `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeModel` (definitions bundle `OAIQ240Bp008` of this split); `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeTranslation` (definitions bundle `OAIQ240Bp020` of this split).
--
--   **Used by.** The proofs of `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.regularityTranslation_continuous_bp240` and `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.regularityTranslation_zero_bp240` of this split import it.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Fredholm/FreeLinearization.lean (declaration OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeTranslation_zero)

import Mathlib
import Definitions.Def_OAIQ240Bp020

section

attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.HigherDimensionalBallPacking.Rigidity.geometricHolder_value _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter
namespace HolderCompletion
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

variable {R S : ℝ} (hRS : R+1 ≤ S) (a : E)
  (u : freeModel (E := E) (Metric.closedBall (0:ℂ) R))

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeTransInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeTransInst2
local instance freeTransInst3_r38fafa_1 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance freeTransInst4_r38fafa_1 : NormedSpace ℝ (HMap ℂ E) := inferInstance
local instance freeTransInst5_r38fafa_1 : NormedAddCommGroup (freeModel (E := E) (Metric.closedBall (0:ℂ) S)) := inferInstance
local instance freeTransInst6_r38fafa_1 : NormedSpace ℝ (freeModel (E := E) (Metric.closedBall (0:ℂ) S)) := inferInstance
@[simp] lemma freeTranslation_zero_bp240 : freeTranslation hRS a u 0=0 := by
  sorry

end HolderCompletion

end

end HigherDimensionalBallPacking.Rigidity
end

end OAI
end
