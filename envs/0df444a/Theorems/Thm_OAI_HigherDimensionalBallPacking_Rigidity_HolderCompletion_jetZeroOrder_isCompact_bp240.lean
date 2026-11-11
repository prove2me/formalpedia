-- Prove2me | Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_jetZeroOrder_isCompact_bp240
-- name    : OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetZeroOrder_isCompact_bp240
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T01:08:30.679968+00:00
-- url     : https://prove2.me/theorems/3f9b3d21-2b2c-43d8-8b42-11852b7f4121
-- title:
--   OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetZeroOrder_isCompact_bp240: intermediate lemma from OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetZeroOrder_isCompact` of [lean/OAI/Geometry/BallPacking/Fredholm/FiniteExtensions.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Fredholm/FiniteExtensions.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion`, with `open scoped ContDiff Topology BoundedContinuousFunction`, `open Set Filter`):
--
--   ```lean
--   lemma jetZeroOrder_isCompact_bp240 [ProperSpace E] (C : HMap ℂ (E →L[ℝ] E))
--       (b : ContDiffBump (0:ℂ))
--       (hC : ∀ z ∉ Metric.closedBall (0:ℂ) b.rIn, valueCLM _ C z = 0) :
--       IsCompactOperator (jetZeroOrder C)
--   ```
--
--   **Definitions.** The statement is written with `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.Ambient`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.COne`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.HMap`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.Holder`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.JetAmbient`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.Pairs` and `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.valueCLM` (definitions bundle `OAIQ240Bp000` of this split); `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.zeroOrderInst1` and `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.zeroOrderInst2` (definitions bundle `OAIQ240Bp001` of this split); `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetZeroOrder` (definitions bundle `OAIQ240Bp011` of this split).
--
--   **Used by.** The proofs of `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedPrincipal_add_compact_fredholm_bp240` and `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedZeroOrder_compact_bp240` of this split import it.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Fredholm/FiniteExtensions.lean (declaration OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetZeroOrder_isCompact)

import Mathlib
import Definitions.Def_OAIQ240Bp011

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
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
namespace HolderCompletion
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [completeSpaceE : CompleteSpace E]

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.zeroOrderInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.zeroOrderInst2
local instance zeroOrderInst3_r723f11_1 : NormedAddCommGroup (COne ℂ E) := inferInstance
local instance zeroOrderInst4_r723f11_1 : NormedSpace ℝ (COne ℂ E) := inferInstance
local instance zeroOrderInst5_r723f11_1 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance zeroOrderInst6_r723f11_1 : NormedSpace ℝ (HMap ℂ E) := inferInstance
lemma jetZeroOrder_isCompact_bp240 [ProperSpace E] (C : HMap ℂ (E →L[ℝ] E))
    (b : ContDiffBump (0:ℂ))
    (hC : ∀ z ∉ Metric.closedBall (0:ℂ) b.rIn, valueCLM _ C z = 0) :
    IsCompactOperator (jetZeroOrder C) := by
  sorry

end HolderCompletion

end

end HigherDimensionalBallPacking.Rigidity
end

end OAI
end
