-- Prove2me | Theorems.Thm_OAI_CircleSampling_model_no_strict_projection
-- name    : OAI.CircleSampling.model_no_strict_projection
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T22:13:58.277998+00:00
-- url     : https://prove2.me/theorems/cbeeb2ee-8a98-4bec-8c91-a4b574ebf422
-- title:
--   OAI.CircleSampling.model_no_strict_projection: intermediate lemma from OpenAI, Invariant-projection counterexamples for every irrational rotation
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ContinuousCircleWeight.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Invariant-projection counterexamples for every irrational rotation*, OpenAI Math Release, September 27, 2026, result family 293, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CircleSampling.model_no_strict_projection` of [lean/OAI/Analysis/RotationWeights/Convolution.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/RotationWeights/Convolution.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CircleSampling`, with `open MeasureTheory`, `open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators`, `open MeasureTheory Filter Set Submodule`, `open scoped ENNReal NNReal Topology ComplexInnerProductSpace`, `open MeasureTheory Filter Set`, `open scoped ENNReal NNReal Topology ComplexInnerProductSpace`, `open MeasureTheory Filter Set`, `open scoped ENNReal NNReal Topology ComplexInnerProductSpace`, `open MeasureTheory Filter Set`, `open scoped ENNReal NNReal Topology ComplexInnerProductSpace`, `open MeasureTheory Filter Set`, `open scoped ENNReal NNReal Topology ComplexInnerProductSpace`, `open MeasureTheory Filter Set`, `open scoped ComplexInnerProductSpace`, `open MeasureTheory Filter Set`, `open Set`, `open scoped ComplexInnerProductSpace`, `open Set`, `open scoped ComplexInnerProductSpace`, `open MeasureTheory Set Filter Topology`, `open scoped BigOperators ComplexConjugate`, `open MeasureTheory Set Filter`, `open scoped BigOperators ENNReal`, `open Filter Set`, `open scoped Topology`, `open Filter Set`, `open scoped Topology`, `open Set MeasureTheory`, `open scoped BigOperators ENNReal Classical`, `open Filter Set`, `open scoped Topology`, `open Set MeasureTheory`, `open scoped ENNReal Classical`, `open Filter`, `open scoped Topology`, `open Set Filter`, `open scoped Topology`, `open Set Topology`, `open scoped BigOperators`, `open scoped BigOperators`, `open Set`, `open Set`, `open Set`, `open Set MeasureTheory Filter`, `open scoped BigOperators ENNReal Topology Classical`, `open MeasureTheory Set Filter`, `open scoped ENNReal Topology`, `open MeasureTheory Set`, `open MeasureTheory Filter Set`, `open scoped Topology BoundedContinuousFunction`, `open MeasureTheory Set Filter Topology TopologicalSpace`, `open MeasureTheory Set`, `open scoped ENNReal BigOperators Classical`, `open MeasureTheory Set`, `open scoped BigOperators ENNReal Classical`, `open MeasureTheory Set`, `open scoped ENNReal`, `open MeasureTheory Set`, `open scoped ENNReal NNReal`, `open MeasureTheory Set Filter`, `open scoped BigOperators ENNReal Topology`, `open Set MeasureTheory Topology`, `open scoped symmDiff`, `open MeasureTheory Set`, `open scoped ENNReal BigOperators`, `open MeasureTheory Set`, `open scoped ENNReal`, `open MeasureTheory Set`, `open scoped BigOperators ENNReal`, `open MeasureTheory Set`, `open scoped ENNReal NNReal BigOperators`, `open MeasureTheory Set Filter ContinuousCircleWeight`, `open scoped ENNReal BigOperators Topology`):
--
--   ```lean
--   theorem model_no_strict_projection (P : ModelProjectionField)
--       (hp : ∀ᵐ x,0 < modelDiagonal P x ∧ modelDiagonal P x<1) : False
--   ```
--
--   **Definitions.** The statement is written with `OAI.CircleSampling.CircleX` (definitions bundle `OAIQ2Rw000` of this split); `OAI.CircleSampling.ModelProjectionField` and `OAI.CircleSampling.modelDiagonal` (definitions bundle `OAIQ2Rw002` of this split).
--
--   **Used by.** The proof of `OAI.ContinuousCircleWeight.main_theorem` of this split imports it.
-- source:
--   OpenAI, Invariant-projection counterexamples for every irrational rotation, OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 293; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Invariant-projection-counterexamples-for-every-irrational-rotation-September-27-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/RotationWeights/Convolution.lean (declaration OAI.CircleSampling.model_no_strict_projection)

import Mathlib
import Definitions.Def_OAIQ2Rw002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CircleSampling

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace
open MeasureTheory Filter Set
open Set
open scoped ComplexInnerProductSpace
open Set
open scoped ComplexInnerProductSpace
open MeasureTheory Set Filter Topology
open scoped BigOperators ComplexConjugate
open MeasureTheory Set Filter
open scoped BigOperators ENNReal
open Filter Set
open scoped Topology
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped ENNReal Classical
open Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Topology
open scoped BigOperators
open scoped BigOperators
open Set
open Set
open Set
open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology Classical
open MeasureTheory Set Filter
open scoped ENNReal Topology
open MeasureTheory Set
open MeasureTheory Filter Set
open scoped Topology BoundedContinuousFunction
open MeasureTheory Set Filter Topology TopologicalSpace
open MeasureTheory Set
open scoped ENNReal BigOperators Classical
open MeasureTheory Set
open scoped BigOperators ENNReal Classical
open MeasureTheory Set
open scoped ENNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology
open Set MeasureTheory Topology
open scoped symmDiff
open MeasureTheory Set
open scoped ENNReal BigOperators
open MeasureTheory Set
open scoped ENNReal
open MeasureTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators

open MeasureTheory Set Filter ContinuousCircleWeight
open scoped ENNReal BigOperators Topology

theorem model_no_strict_projection (P : ModelProjectionField)
    (hp : ∀ᵐ x,0 < modelDiagonal P x ∧ modelDiagonal P x<1) : False := by
  sorry

end CircleSampling

end

end OAI
end
