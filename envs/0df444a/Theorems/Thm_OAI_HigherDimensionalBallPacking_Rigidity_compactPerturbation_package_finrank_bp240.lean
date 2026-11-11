-- Prove2me | Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_compactPerturbation_package_finrank_bp240
-- name    : OAI.HigherDimensionalBallPacking.Rigidity.compactPerturbation_package_finrank_bp240
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T22:41:17.66992+00:00
-- url     : https://prove2.me/theorems/7c198f47-2279-4c57-beee-8a537917401e
-- title:
--   OAI.HigherDimensionalBallPacking.Rigidity.compactPerturbation_package_finrank_bp240: intermediate lemma from OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.HigherDimensionalBallPacking.Rigidity.compactPerturbation_package_finrank` of [lean/OAI/Geometry/BallPacking/Fredholm/CompactFredholmAlternative.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Fredholm/CompactFredholmAlternative.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.HigherDimensionalBallPacking.Rigidity`, with `open Function`, `open Set`):
--
--   ```lean
--    theorem compactPerturbation_package_finrank_bp240 (T : E →L[ℝ] E) (hT : IsCompactOperator T)
--       (pkg : (ContinuousLinearMap.id ℝ E+T).FredholmPackage) :
--       Module.finrank ℝ pkg.decDom.X₀=Module.finrank ℝ pkg.decCodom.X₀
--   ```
--
--   **Used by.** The proof of `OAI.HigherDimensionalBallPacking.Rigidity.framed_compact_perturbation_fredholm_bp240` of this split imports it.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Fredholm/CompactFredholmAlternative.lean (declaration OAI.HigherDimensionalBallPacking.Rigidity.compactPerturbation_package_finrank)

import Mathlib

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HigherDimensionalBallPacking.Rigidity
open Function
open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

 theorem compactPerturbation_package_finrank_bp240 (T : E →L[ℝ] E) (hT : IsCompactOperator T)
    (pkg : (ContinuousLinearMap.id ℝ E+T).FredholmPackage) :
    Module.finrank ℝ pkg.decDom.X₀=Module.finrank ℝ pkg.decCodom.X₀ := by
  sorry

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end
