-- Prove2me | Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_ProperIndexZeroPath_endpoint_exists_bp240
-- name    : OAI.HigherDimensionalBallPacking.Rigidity.ProperIndexZeroPath.endpoint_exists_bp240
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:50:21.26435+00:00
-- url     : https://prove2.me/theorems/e24f39e7-d5cf-4fc4-a18c-0be18b99f256
-- title:
--   OAI.HigherDimensionalBallPacking.Rigidity.ProperIndexZeroPath.endpoint_exists_bp240: intermediate lemma from OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.HigherDimensionalBallPacking.Rigidity.ProperIndexZeroPath.endpoint_exists` of [lean/OAI/Geometry/BallPacking/Continuation/ProperPaths.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Continuation/ProperPaths.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.HigherDimensionalBallPacking.Rigidity`, with `open scoped ContDiff Topology`, `open Set Function Filter`):
--
--   ```lean
--    theorem ProperIndexZeroPath.endpoint_exists_bp240 {F : ℝ × X → Y} {U : Set X}
--       (h : ProperIndexZeroPath F U) : ∃ x∈U,F (1,x)=0
--   ```
--
--   **Definitions.** The statement is written with `OAI.HigherDimensionalBallPacking.Rigidity.ProperIndexZeroPath` (definitions bundle `OAIQ240Bp017` of this split).
--
--   **Used by.** The proof of `OAI.HigherDimensionalBallPacking.main_theorem` of this split imports it.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Continuation/ProperPaths.lean (declaration OAI.HigherDimensionalBallPacking.Rigidity.ProperIndexZeroPath.endpoint_exists)

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
open scoped ContDiff Topology
open Set Function Filter
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

 theorem ProperIndexZeroPath.endpoint_exists_bp240 {F : ℝ × X → Y} {U : Set X}
    (h : ProperIndexZeroPath F U) : ∃ x∈U,F (1,x)=0 := by
  sorry

end

end HigherDimensionalBallPacking.Rigidity
end

end OAI
end
