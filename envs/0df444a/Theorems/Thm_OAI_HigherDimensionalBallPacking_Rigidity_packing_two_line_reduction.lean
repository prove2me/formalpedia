-- Prove2me | Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_packing_two_line_reduction
-- name    : OAI.HigherDimensionalBallPacking.Rigidity.packing_two_line_reduction
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T16:41:09.206995+00:00
-- url     : https://prove2.me/theorems/96856005-06f4-485d-85f7-0f166d088ce4
-- title:
--   OAI.HigherDimensionalBallPacking.Rigidity.packing_two_line_reduction: intermediate lemma from OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.packing_necessity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.HigherDimensionalBallPacking.Rigidity.packing_two_line_reduction` of [lean/OAI/Geometry/BallPacking/BallPacking/Rigidity/CorrectedInfinity.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/BallPacking/Rigidity/CorrectedInfinity.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.HigherDimensionalBallPacking.Rigidity`, with `open scoped ContDiff Topology`, `open Set Function Filter MeasureTheory`):
--
--   ```lean
--   theorem packing_two_line_reduction {n : ℕ} {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
--       (hp : HasPacking n 2 1 ![a,b]) :
--       ∃ (J : Phase n → End n) (p q : Phase n), ContDiff ℝ ∞ J ∧
--         (∀ x, Compatible (J x)) ∧ HasCompactSupport (fun x => J x - standardJ n) ∧
--         tsupport (fun x => J x - standardJ n) ⊆ openBall n 1 ∧ p ≠ q ∧
--         ∀ u : ℂ → Phase n, AffineLineCurve J p q u → a+b ≤ 1
--   ```
--
--   **Definitions.** The statement is written with `OAI.HigherDimensionalBallPacking.Rigidity.Compatible`, `OAI.HigherDimensionalBallPacking.Rigidity.End` and `OAI.HigherDimensionalBallPacking.Rigidity.standardJ` (definitions bundle `OAIQ10Bp000` of this split); `OAI.HigherDimensionalBallPacking.Rigidity.AffineLineCurve` (definitions bundle `OAIQ10Bp002` of this split); `OAI.HigherDimensionalBallPacking.HasPacking`, `OAI.HigherDimensionalBallPacking.Phase` and `OAI.HigherDimensionalBallPacking.openBall` (the published bundle `Def_BallPackingNecessity`).
--
--   **Used by.** The proof of `OAI.HigherDimensionalBallPacking.normalized_two_ball_obstruction` of this split imports it.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/BallPacking/Rigidity/CorrectedInfinity.lean (declaration OAI.HigherDimensionalBallPacking.Rigidity.packing_two_line_reduction)

import Mathlib
import Definitions.Def_BallPackingNecessity
import Definitions.Def_OAIQ10Bp002

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

theorem packing_two_line_reduction {n : ℕ} {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hp : HasPacking n 2 1 ![a,b]) :
    ∃ (J : Phase n → End n) (p q : Phase n), ContDiff ℝ ∞ J ∧
      (∀ x, Compatible (J x)) ∧ HasCompactSupport (fun x => J x - standardJ n) ∧
      tsupport (fun x => J x - standardJ n) ⊆ openBall n 1 ∧ p ≠ q ∧
      ∀ u : ℂ → Phase n, AffineLineCurve J p q u → a+b ≤ 1 := by
  sorry

end HigherDimensionalBallPacking.Rigidity
end

end OAI
end
