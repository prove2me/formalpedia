-- Prove2me | Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_jetValue_translate_tendsto_bp240
-- name    : OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetValue_translate_tendsto_bp240
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T01:52:14.071962+00:00
-- url     : https://prove2.me/theorems/dd9b24e0-308d-41c3-8968-241cce1f014a
-- title:
--   OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetValue_translate_tendsto_bp240: intermediate lemma from OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetValue_translate_tendsto` of [lean/OAI/Geometry/BallPacking/Compactness/AffineCorrectionInfinity.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Compactness/AffineCorrectionInfinity.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion`, with `open scoped ContDiff Topology BoundedContinuousFunction`, `open Set Filter`):
--
--   ```lean
--   lemma jetValue_translate_tendsto_bp240 (u : COne D E) :
--       Tendsto (fun t => holderTranslate t (jetValueCLM _ u)) (𝓝 0) (𝓝 (jetValueCLM _ u))
--   ```
--
--   **Definitions.** The statement is written with `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.Ambient`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.COne`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.COneHolder`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.HMap`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.Holder`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.JetAmbient`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.Pairs` and `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetValueCLM` (definitions bundle `OAIQ240Bp000` of this split); `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.holderTranslate` (definitions bundle `OAIQ240Bp025` of this split).
--
--   **Used by.** The proof of `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.regularityTranslation_continuous_bp240` of this split imports it.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Compactness/AffineCorrectionInfinity.lean (declaration OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetValue_translate_tendsto)

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
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion
variable {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.transInst1
local instance transInst2_r31227b_1 : NormedSpace ℝ (HMap D E) := inferInstance
local instance transInst3_r31227b_1 : NormedAddCommGroup (COne D E) := inferInstance
local instance transInst4_r31227b_1 : NormedSpace ℝ (COne D E) := inferInstance
lemma jetValue_translate_tendsto_bp240 (u : COne D E) :
    Tendsto (fun t => holderTranslate t (jetValueCLM _ u)) (𝓝 0) (𝓝 (jetValueCLM _ u)) := by
  sorry

end HigherDimensionalBallPacking.Rigidity.HolderCompletion

end

end OAI
end
