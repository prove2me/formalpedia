-- Prove2me | Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_finite_separating_family_bp240
-- name    : OAI.HigherDimensionalBallPacking.Rigidity.finite_separating_family_bp240
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T01:07:44.696248+00:00
-- url     : https://prove2.me/theorems/daccf9a1-ad21-4940-84c5-d4cccdd04aa4
-- title:
--   OAI.HigherDimensionalBallPacking.Rigidity.finite_separating_family_bp240: intermediate lemma from OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.HigherDimensionalBallPacking.Rigidity.finite_separating_family` of [lean/OAI/Geometry/BallPacking/Fredholm/FreeLinearization.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Fredholm/FreeLinearization.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.HigherDimensionalBallPacking.Rigidity`, with `open Set Function`):
--
--   ```lean
--    theorem finite_separating_family_bp240 (L : I → E →L[ℝ] F)
--       (hL : ∀ v : E, (∀ i, L i v=0) → v=0) :
--       ∃ s : Finset I, ∀ v : E, (∀ i ∈ s, L i v=0) → v=0
--   ```
--
--   **Used by.** The proofs of `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.regularityTranslation_continuous_bp240` and `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.regularityTranslation_smooth_bp240` of this split import it.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Fredholm/FreeLinearization.lean (declaration OAI.HigherDimensionalBallPacking.Rigidity.finite_separating_family)

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
variable {E F I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

 theorem finite_separating_family_bp240 (L : I → E →L[ℝ] F)
    (hL : ∀ v : E, (∀ i, L i v=0) → v=0) :
    ∃ s : Finset I, ∀ v : E, (∀ i ∈ s, L i v=0) → v=0 := by
  sorry

end

end HigherDimensionalBallPacking.Rigidity
end

end OAI
end
