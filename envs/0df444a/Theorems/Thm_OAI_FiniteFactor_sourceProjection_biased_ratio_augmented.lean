-- Prove2me | Theorems.Thm_OAI_FiniteFactor_sourceProjection_biased_ratio_augmented
-- name    : OAI.FiniteFactor.sourceProjection_biased_ratio_augmented
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T23:36:31.317322+00:00
-- url     : https://prove2.me/theorems/9bb3d6d8-e34d-4bf8-83bd-254aaab6feb1
-- title:
--   OAI.FiniteFactor.sourceProjection_biased_ratio_augmented: intermediate lemma from OpenAI, Invariant-projection counterexamples for every irrational rotation
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.FiniteFactor.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Invariant-projection counterexamples for every irrational rotation*, OpenAI Math Release, September 27, 2026, result family 293, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.FiniteFactor.sourceProjection_biased_ratio_augmented` of [lean/OAI/Analysis/FiniteFactor/BiasedPairs/RealIdentity.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FiniteFactor/BiasedPairs/RealIdentity.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.FiniteFactor`, with `open MeasureTheory Filter`, `open scoped ENNReal`):
--
--   ```lean
--   theorem sourceProjection_biased_ratio_augmented (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ)
--       (hs : SourceOrderedTorusSampling θ)
--       {p : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
--       (hp : p ∈ sourceAlgebra θ) (hproj : IsStarProjection p)
--       (hinv : (1-p)*sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg*p = 0)
--       (j : ℕ) :
--       ∀ᵐ ω ∂sourceBiasedLaw j,
--         ∃ D : SourceFiberHilbert →L[ℂ] SourceFiberHilbert,
--           ‖D‖ ≤ 1 ∧
--           (∀ (v : SourceFiberHilbert) (k : ℤ), D v k =
--             (sourceCocycle θ sourceLogWeight k (sourceBiasedEndpoint (fun _ => true) ω) /
--               sourceCocycle θ sourceLogWeight k (sourceBiasedEndpoint (fun _ => false) ω) : ℂ) * v k) ∧
--           (1-sourceOperatorField p (sourceBiasedEndpoint (fun _ => true) ω))*D*
--             sourceOperatorField p (sourceBiasedEndpoint (fun _ => false) ω) = 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.FiniteFactor.SourceAngles`, `OAI.FiniteFactor.SourceBiasedSample`, `OAI.FiniteFactor.SourceCoordinate`, `OAI.FiniteFactor.SourceFiberHilbert`, `OAI.FiniteFactor.SourceHilbert`, `OAI.FiniteFactor.SourceOrderedTorusSampling`, `OAI.FiniteFactor.sourceAlgebra`, `OAI.FiniteFactor.sourceBiasedEndpoint`, `OAI.FiniteFactor.sourceBiasedLaw`, `OAI.FiniteFactor.sourceBlockSize`, `OAI.FiniteFactor.sourceCocycle`, `OAI.FiniteFactor.sourceLogWeight`, `OAI.FiniteFactor.sourceMeasure`, `OAI.FiniteFactor.sourceOperatorField` and `OAI.FiniteFactor.SourceAngles.nonneg` (definitions bundle `OAIQ3Ff000` of this split); `OAI.FiniteFactor.sourceLogWeight_nonneg` and `OAI.FiniteFactor.sourceOperator` (definitions bundle `OAIQ3Ff002` of this split).
--
--   **Used by.** The proofs of `OAI.FiniteFactor.sourceProjectionEvent_error_pointwise` and `OAI.FiniteFactor.sourceProjectionEvent_mass_upper` of this split import it.
-- source:
--   OpenAI, Invariant-projection counterexamples for every irrational rotation, OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 293; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Invariant-projection-counterexamples-for-every-irrational-rotation-September-27-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FiniteFactor/BiasedPairs/RealIdentity.lean (declaration OAI.FiniteFactor.sourceProjection_biased_ratio_augmented)

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

theorem sourceProjection_biased_ratio_augmented (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ)
    (hs : SourceOrderedTorusSampling θ)
    {p : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hp : p ∈ sourceAlgebra θ) (hproj : IsStarProjection p)
    (hinv : (1-p)*sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg*p = 0)
    (j : ℕ) :
    ∀ᵐ ω ∂sourceBiasedLaw j,
      ∃ D : SourceFiberHilbert →L[ℂ] SourceFiberHilbert,
        ‖D‖ ≤ 1 ∧
        (∀ (v : SourceFiberHilbert) (k : ℤ), D v k =
          (sourceCocycle θ sourceLogWeight k (sourceBiasedEndpoint (fun _ => true) ω) /
            sourceCocycle θ sourceLogWeight k (sourceBiasedEndpoint (fun _ => false) ω) : ℂ) * v k) ∧
        (1-sourceOperatorField p (sourceBiasedEndpoint (fun _ => true) ω))*D*
          sourceOperatorField p (sourceBiasedEndpoint (fun _ => false) ω) = 0 := by
  sorry

end
end FiniteFactor

end OAI
end
