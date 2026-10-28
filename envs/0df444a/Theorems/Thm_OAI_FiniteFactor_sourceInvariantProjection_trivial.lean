-- Prove2me | Theorems.Thm_OAI_FiniteFactor_sourceInvariantProjection_trivial
-- name    : OAI.FiniteFactor.sourceInvariantProjection_trivial
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T23:32:27.740141+00:00
-- url     : https://prove2.me/theorems/52e9cece-0d67-4ee8-9d7e-0ef857104499
-- title:
--   OAI.FiniteFactor.sourceInvariantProjection_trivial: intermediate lemma from OpenAI, Invariant-projection counterexamples for every irrational rotation
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.FiniteFactor.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Invariant-projection counterexamples for every irrational rotation*, OpenAI Math Release, September 27, 2026, result family 293, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.FiniteFactor.sourceInvariantProjection_trivial` of [lean/OAI/Analysis/FiniteFactor/CrossedProduct/InvariantProjection.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FiniteFactor/CrossedProduct/InvariantProjection.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.FiniteFactor`, with `open MeasureTheory Filter`, `open scoped Topology`):
--
--   ```lean
--   theorem sourceInvariantProjection_trivial
--       (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ) (hr : SourceRationalIndependent θ)
--       (hs : SourceOrderedTorusSampling θ) (hphase : ∃ J, SourceSecondPhasesFrom θ J)
--       {p : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
--       (hp : p ∈ sourceAlgebra θ) (hproj : IsStarProjection p)
--       (hinv : (1-p)*sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg*p = 0) :
--       p = 0 ∨ p = 1
--   ```
--
--   **Definitions.** The statement is written with `OAI.FiniteFactor.SourceAngles`, `OAI.FiniteFactor.SourceCoordinate`, `OAI.FiniteFactor.SourceHilbert`, `OAI.FiniteFactor.SourceOrderedTorusSampling`, `OAI.FiniteFactor.SourceRationalIndependent`, `OAI.FiniteFactor.SourceSecondPhasesFrom`, `OAI.FiniteFactor.sourceAlgebra`, `OAI.FiniteFactor.sourceBlockSize`, `OAI.FiniteFactor.sourceLogWeight`, `OAI.FiniteFactor.sourceMeasure` and `OAI.FiniteFactor.SourceAngles.nonneg` (definitions bundle `OAIQ3Ff000` of this split); `OAI.FiniteFactor.sourceLogWeight_nonneg` and `OAI.FiniteFactor.sourceOperator` (definitions bundle `OAIQ3Ff002` of this split).
--
--   **Used by.** The proof of `OAI.FiniteFactor.main_theorem` of this split imports it.
-- source:
--   OpenAI, Invariant-projection counterexamples for every irrational rotation, OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 293; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Invariant-projection-counterexamples-for-every-irrational-rotation-September-27-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FiniteFactor/CrossedProduct/InvariantProjection.lean (declaration OAI.FiniteFactor.sourceInvariantProjection_trivial)

import Mathlib
import Definitions.Def_OAIQ3Ff002

section

attribute [-instance] _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped Topology
noncomputable section

theorem sourceInvariantProjection_trivial
    (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ) (hr : SourceRationalIndependent θ)
    (hs : SourceOrderedTorusSampling θ) (hphase : ∃ J, SourceSecondPhasesFrom θ J)
    {p : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hp : p ∈ sourceAlgebra θ) (hproj : IsStarProjection p)
    (hinv : (1-p)*sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg*p = 0) :
    p = 0 ∨ p = 1 := by
  sorry

end
end FiniteFactor

end OAI
end
