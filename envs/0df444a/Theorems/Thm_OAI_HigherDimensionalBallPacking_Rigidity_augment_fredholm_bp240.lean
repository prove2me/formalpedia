-- Prove2me | Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_augment_fredholm_bp240
-- name    : OAI.HigherDimensionalBallPacking.Rigidity.augment_fredholm_bp240
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T22:41:18.922+00:00
-- url     : https://prove2.me/theorems/c977420f-1a57-40c5-b1ab-3c24ba4e5443
-- title:
--   OAI.HigherDimensionalBallPacking.Rigidity.augment_fredholm_bp240: intermediate lemma from OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.HigherDimensionalBallPacking.Rigidity.augment_fredholm` of [lean/OAI/Geometry/BallPacking/Fredholm/NonlinearReduction.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Fredholm/NonlinearReduction.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.HigherDimensionalBallPacking.Rigidity`, with `open scoped ContDiff Topology`, `open Set Function Filter`):
--
--   ```lean
--   lemma augment_fredholm_bp240 (hG : Surjective (D.coprod E.subtypeL)) :
--       (D.coprod E.subtypeL).IsFredholm
--   ```
--
--   **Used by.** The proof of `OAI.HigherDimensionalBallPacking.Rigidity.ProperIndexZeroPath.endpoint_exists_bp240` of this split imports it.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Fredholm/NonlinearReduction.lean (declaration OAI.HigherDimensionalBallPacking.Rigidity.augment_fredholm)

import Mathlib

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HigherDimensionalBallPacking.Rigidity
open scoped ContDiff Topology
open Set Function Filter
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
variable {D : X →L[ℝ] Y} (hD : D.IsFredholm)
  (E : Submodule ℝ Y) [FiniteDimensional ℝ E]

include hD in
lemma augment_fredholm_bp240 (hG : Surjective (D.coprod E.subtypeL)) :
    (D.coprod E.subtypeL).IsFredholm := by
  sorry

end HigherDimensionalBallPacking.Rigidity
end

end OAI
end
