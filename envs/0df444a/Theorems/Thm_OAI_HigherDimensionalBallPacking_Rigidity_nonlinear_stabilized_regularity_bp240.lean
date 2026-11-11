-- Prove2me | Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_nonlinear_stabilized_regularity_bp240
-- name    : OAI.HigherDimensionalBallPacking.Rigidity.nonlinear_stabilized_regularity_bp240
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T01:07:49.868478+00:00
-- url     : https://prove2.me/theorems/ac295f03-f807-4dda-bf82-5363f998fa32
-- title:
--   OAI.HigherDimensionalBallPacking.Rigidity.nonlinear_stabilized_regularity_bp240: intermediate lemma from OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.HigherDimensionalBallPacking.Rigidity.nonlinear_stabilized_regularity` of [lean/OAI/Geometry/BallPacking/Fredholm/TranslationContinuity.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Fredholm/TranslationContinuity.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.HigherDimensionalBallPacking.Rigidity`, with `open scoped ContDiff Topology`, `open Set Function Filter`):
--
--   ```lean
--   lemma nonlinear_stabilized_regularity_bp240 {f : E → F} (hf : ContDiff ℝ ∞ f)
--       {P : E →L[ℝ] F} {v : X → E} {x : X} (hP : HasFDerivAt f P (v x))
--       (Q : E →L[ℝ] D) (L : F × D →L[ℝ] E) (hL : LeftInverse L (P.prod Q))
--       (hv : ContinuousAt v x) (hQ : ContDiffAt ℝ ∞ (fun t => Q (v t)) x)
--       (he : ∀ᶠ t in 𝓝 x, f (v t)=0) : ContDiffAt ℝ ∞ v x
--   ```
--
--   **Used by.** The proof of `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.regularityTranslation_smooth_bp240` of this split imports it.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Fredholm/TranslationContinuity.lean (declaration OAI.HigherDimensionalBallPacking.Rigidity.nonlinear_stabilized_regularity)

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
variable {X E F D : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup D] [NormedSpace ℝ D]

lemma nonlinear_stabilized_regularity_bp240 {f : E → F} (hf : ContDiff ℝ ∞ f)
    {P : E →L[ℝ] F} {v : X → E} {x : X} (hP : HasFDerivAt f P (v x))
    (Q : E →L[ℝ] D) (L : F × D →L[ℝ] E) (hL : LeftInverse L (P.prod Q))
    (hv : ContinuousAt v x) (hQ : ContDiffAt ℝ ∞ (fun t => Q (v t)) x)
    (he : ∀ᶠ t in 𝓝 x, f (v t)=0) : ContDiffAt ℝ ∞ v x := by
  sorry

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end
