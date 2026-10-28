-- Prove2me | Theorems.Thm_OAI_FiniteFactor_sourceProjectionEvent_error_pointwise
-- name    : OAI.FiniteFactor.sourceProjectionEvent_error_pointwise
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T23:34:37.635985+00:00
-- url     : https://prove2.me/theorems/a5265451-a76c-4894-bc3f-c5360f947d47
-- title:
--   OAI.FiniteFactor.sourceProjectionEvent_error_pointwise: intermediate lemma from OpenAI, Invariant-projection counterexamples for every irrational rotation
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.FiniteFactor.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Invariant-projection counterexamples for every irrational rotation*, OpenAI Math Release, September 27, 2026, result family 293, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.FiniteFactor.sourceProjectionEvent_error_pointwise` of [lean/OAI/Analysis/FiniteFactor/CrossedProduct/ProjectionErrors.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FiniteFactor/CrossedProduct/ProjectionErrors.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.FiniteFactor`, with `open MeasureTheory Filter`, `open scoped ENNReal`):
--
--   ```lean
--   theorem sourceProjectionEvent_error_pointwise (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ)
--       (hs : SourceOrderedTorusSampling θ)
--       {p : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
--       (hp : p ∈ sourceAlgebra θ) (hproj : IsStarProjection p)
--       (hinv : (1-p)*sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg*p = 0)
--       (j : ℕ) (hphase : SourceSecondPhasesFrom θ j) (n : ℕ) :
--       ∀ᵐ ω ∂sourceBiasedLaw j, ω ∈ sourceProjectionEvent p j →
--         ‖sourceTruncatedCoefficient θ p j n ω‖ ≤ Real.exp (-(sourceStage j).L) +
--           sourceOmittedError θ hθ p j hphase n false ω + sourceOmittedError θ hθ p j hphase n true ω
--   ```
--
--   **Definitions.** The statement is written with `OAI.FiniteFactor.SourceAngles`, `OAI.FiniteFactor.SourceBiasedSample`, `OAI.FiniteFactor.SourceCoordinate`, `OAI.FiniteFactor.SourceHilbert`, `OAI.FiniteFactor.SourceOrderedTorusSampling`, `OAI.FiniteFactor.SourceSecondPhasesFrom`, `OAI.FiniteFactor.sourceAlgebra`, `OAI.FiniteFactor.sourceBiasedLaw`, `OAI.FiniteFactor.sourceBlockSize`, `OAI.FiniteFactor.sourceLogWeight`, `OAI.FiniteFactor.sourceMeasure`, `OAI.FiniteFactor.sourceStage`, `OAI.FiniteFactor.sourceStageState`, `OAI.FiniteFactor.SourceAngles.nonneg` and `OAI.FiniteFactor.SourceStageChoice` (definitions bundle `OAIQ3Ff000` of this split); `OAI.FiniteFactor.sourceLogWeight_nonneg`, `OAI.FiniteFactor.sourceOmittedError`, `OAI.FiniteFactor.sourceOperator`, `OAI.FiniteFactor.sourceProjectionEvent` and `OAI.FiniteFactor.sourceTruncatedCoefficient` (definitions bundle `OAIQ3Ff002` of this split).
--
--   **Used by.** The proof of `OAI.FiniteFactor.sourceProjectionEvent_mass_upper` of this split imports it.
-- source:
--   OpenAI, Invariant-projection counterexamples for every irrational rotation, OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 293; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Invariant-projection-counterexamples-for-every-irrational-rotation-September-27-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FiniteFactor/CrossedProduct/ProjectionErrors.lean (declaration OAI.FiniteFactor.sourceProjectionEvent_error_pointwise)

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
open scoped ENNReal
noncomputable section

theorem sourceProjectionEvent_error_pointwise (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ)
    (hs : SourceOrderedTorusSampling θ)
    {p : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hp : p ∈ sourceAlgebra θ) (hproj : IsStarProjection p)
    (hinv : (1-p)*sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg*p = 0)
    (j : ℕ) (hphase : SourceSecondPhasesFrom θ j) (n : ℕ) :
    ∀ᵐ ω ∂sourceBiasedLaw j, ω ∈ sourceProjectionEvent p j →
      ‖sourceTruncatedCoefficient θ p j n ω‖ ≤ Real.exp (-(sourceStage j).L) +
        sourceOmittedError θ hθ p j hphase n false ω + sourceOmittedError θ hθ p j hphase n true ω := by
  sorry

end
end FiniteFactor

end OAI
end
