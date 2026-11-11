-- Prove2me | Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_fredholm_stabilized_leftInverse_bp240
-- name    : OAI.HigherDimensionalBallPacking.Rigidity.fredholm_stabilized_leftInverse_bp240
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T01:07:49.317055+00:00
-- url     : https://prove2.me/theorems/04940795-c061-4fc4-98e1-9e6f26ae81b4
-- title:
--   OAI.HigherDimensionalBallPacking.Rigidity.fredholm_stabilized_leftInverse_bp240: intermediate lemma from OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.HigherDimensionalBallPacking.Rigidity.fredholm_stabilized_leftInverse` of [lean/OAI/Geometry/BallPacking/Fredholm/FreeLinearization.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Fredholm/FreeLinearization.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.HigherDimensionalBallPacking.Rigidity`, with `open Set Function`):
--
--   ```lean
--    theorem fredholm_stabilized_leftInverse_bp240 (P : E →L[ℝ] F) (hP : P.IsFredholm)
--       (Q : E →L[ℝ] D) (hQ : Injective (Q.comp P.ker.subtypeL)) :
--       (P.prod Q).HasLeftInverse
--   ```
--
--   **Used by.** The proofs of `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.regularityTranslation_continuous_bp240` and `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.regularityTranslation_smooth_bp240` of this split import it.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Fredholm/FreeLinearization.lean (declaration OAI.HigherDimensionalBallPacking.Rigidity.fredholm_stabilized_leftInverse)

import Mathlib

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open Set Function
variable {E F D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]

 theorem fredholm_stabilized_leftInverse_bp240 (P : E →L[ℝ] F) (hP : P.IsFredholm)
    (Q : E →L[ℝ] D) (hQ : Injective (Q.comp P.ker.subtypeL)) :
    (P.prod Q).HasLeftInverse := by
  sorry

end

end HigherDimensionalBallPacking.Rigidity
end

end OAI
end
