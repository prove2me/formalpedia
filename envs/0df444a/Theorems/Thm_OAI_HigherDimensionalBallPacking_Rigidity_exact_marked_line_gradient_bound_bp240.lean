-- Prove2me | Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_exact_marked_line_gradient_bound_bp240
-- name    : OAI.HigherDimensionalBallPacking.Rigidity.exact_marked_line_gradient_bound_bp240
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T22:44:51.189197+00:00
-- url     : https://prove2.me/theorems/481846c8-3edb-4782-862f-33e4d70d20c1
-- title:
--   OAI.HigherDimensionalBallPacking.Rigidity.exact_marked_line_gradient_bound_bp240: intermediate lemma from OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.HigherDimensionalBallPacking.Rigidity.exact_marked_line_gradient_bound` of [lean/OAI/Geometry/BallPacking/Compactness/MarkedCurves.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Compactness/MarkedCurves.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.HigherDimensionalBallPacking.Rigidity`, with `open scoped ContDiff Topology`, `open Set Function Filter MeasureTheory`, `open HolderCompletion`, `open scoped BoundedContinuousFunction`):
--
--   ```lean
--   theorem exact_marked_line_gradient_bound_bp240 {J : Phase n → End n}
--       (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x,Compatible (J x))
--       (hJc : HasCompactSupport (fun x => J x-standardJ n))
--       {S T : ℝ} (hST : S<T) (hT : T<1)
--       (hout : ∀ x,S < capacity x →J x=standardJ n) (p q : Phase n) :
--       ∃ M : ℝ,0<M ∧ ∀ t∈Icc (0:ℝ) 1,∀ (u : ℂ → Phase n),
--         AffineLineCurve (lineHomotopy J t) p q u →∀ z : ℂ,‖fderiv ℝ u z‖≤M
--   ```
--
--   **Definitions.** The statement is written with `OAI.HigherDimensionalBallPacking.Rigidity.AffineLineCurve`, `OAI.HigherDimensionalBallPacking.Rigidity.Compatible`, `OAI.HigherDimensionalBallPacking.Rigidity.End`, `OAI.HigherDimensionalBallPacking.Rigidity.lineHomotopy` and `OAI.HigherDimensionalBallPacking.Rigidity.standardJ` (definitions bundle `OAIQ240Bp000` of this split); `OAI.HigherDimensionalBallPacking.Phase` and `OAI.HigherDimensionalBallPacking.capacity` (the published bundle `Def_BallPacking`).
--
--   **Used by.** The proof of `OAI.HigherDimensionalBallPacking.Rigidity.exact_marked_local_jet_cauchy_bp240` of this split imports it.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Compactness/MarkedCurves.lean (declaration OAI.HigherDimensionalBallPacking.Rigidity.exact_marked_line_gradient_bound)

import Mathlib
import Definitions.Def_BallPacking
import Definitions.Def_OAIQ240Bp000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HigherDimensionalBallPacking.Rigidity
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open HolderCompletion
open scoped BoundedContinuousFunction
variable {n : ℕ}

theorem exact_marked_line_gradient_bound_bp240 {J : Phase n → End n}
    (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x,Compatible (J x))
    (hJc : HasCompactSupport (fun x => J x-standardJ n))
    {S T : ℝ} (hST : S<T) (hT : T<1)
    (hout : ∀ x,S < capacity x →J x=standardJ n) (p q : Phase n) :
    ∃ M : ℝ,0<M ∧ ∀ t∈Icc (0:ℝ) 1,∀ (u : ℂ → Phase n),
      AffineLineCurve (lineHomotopy J t) p q u →∀ z : ℂ,‖fderiv ℝ u z‖≤M := by
  sorry

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end
