-- Prove2me | Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_compact_subset_bump_inner_bp240
-- name    : OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compact_subset_bump_inner_bp240
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T01:51:43.509646+00:00
-- url     : https://prove2.me/theorems/4057b436-11dd-4958-a2dc-936402cf4d9f
-- title:
--   OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compact_subset_bump_inner_bp240: intermediate lemma from OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compact_subset_bump_inner` of [lean/OAI/Geometry/BallPacking/Fredholm/CompactFredholmAlternative.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Fredholm/CompactFredholmAlternative.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion`, with `open scoped ContDiff Topology BoundedContinuousFunction`, `open Set Filter`):
--
--   ```lean
--   lemma compact_subset_bump_inner_bp240 {K : Set ℂ} (hK : IsCompact K) :
--       ∃ b : ContDiffBump (0:ℂ), K ⊆ Metric.closedBall (0:ℂ) b.rIn
--   ```
--
--   **Used by.** The proofs of `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actualMarkedChart_derivative_fredholm_bp240`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedPrincipal_add_compact_fredholm_bp240`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedZeroOrder_compact_bp240` and `OAI.HigherDimensionalBallPacking.Rigidity.adapted_line_continuation_data_bp240` of this split import it.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Fredholm/CompactFredholmAlternative.lean (declaration OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compact_subset_bump_inner)

import Mathlib

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

lemma compact_subset_bump_inner_bp240 {K : Set ℂ} (hK : IsCompact K) :
    ∃ b : ContDiffBump (0:ℂ), K ⊆ Metric.closedBall (0:ℂ) b.rIn := by
  sorry

end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end
