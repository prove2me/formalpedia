-- Prove2me | Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_jetTest_separates_bp240
-- name    : OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetTest_separates_bp240
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T01:54:04.068224+00:00
-- url     : https://prove2.me/theorems/9158aecc-8e9b-49c8-8328-f0c5cf68f4dd
-- title:
--   OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetTest_separates_bp240: intermediate lemma from OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetTest_separates` of [lean/OAI/Geometry/BallPacking/Fredholm/FreeLinearization.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Fredholm/FreeLinearization.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion`, with `open scoped Topology BoundedContinuousFunction ContDiff`, `open Set Function Filter MeasureTheory`):
--
--   ```lean
--   lemma jetTest_separates_bp240 (u : COne ℂ E) (hu : ∀ g : PlaneTest, jetTestCLM g u=0) : u=0
--   ```
--
--   **Definitions.** The statement is written with `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.Ambient`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.COne`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.Holder`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.JetAmbient` and `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.Pairs` (definitions bundle `OAIQ240Bp000` of this split); `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.PlaneTest` (definitions bundle `OAIQ240Bp001` of this split); `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetTestCLM` (definitions bundle `OAIQ240Bp017` of this split).
--
--   **Used by.** The proofs of `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.regularityTranslation_continuous_bp240` and `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.regularityTranslation_smooth_bp240` of this split import it.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Fredholm/FreeLinearization.lean (declaration OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetTest_separates)

import Mathlib
import Definitions.Def_OAIQ240Bp017

section

attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped Topology BoundedContinuousFunction ContDiff
open Set Function Filter MeasureTheory
namespace HolderCompletion
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

local instance testInst1_r9035f0_1 : NormedAddCommGroup (COne ℂ E) := inferInstance
local instance testInst2_r9035f0_1 : NormedSpace ℝ (COne ℂ E) := inferInstance
lemma jetTest_separates_bp240 (u : COne ℂ E) (hu : ∀ g : PlaneTest, jetTestCLM g u=0) : u=0 := by
  sorry

end HolderCompletion

end

end HigherDimensionalBallPacking.Rigidity
end

end OAI
end
