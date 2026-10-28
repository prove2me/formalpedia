-- Prove2me | Theorems.Thm_OAI_FiniteFactor_exists_source_prepared_finite
-- name    : OAI.FiniteFactor.exists_source_prepared_finite
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T23:33:36.425344+00:00
-- url     : https://prove2.me/theorems/db572fb8-9937-4d9a-b133-3d43696e0e59
-- title:
--   OAI.FiniteFactor.exists_source_prepared_finite: intermediate lemma from OpenAI, Invariant-projection counterexamples for every irrational rotation
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.FiniteFactor.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Invariant-projection counterexamples for every irrational rotation*, OpenAI Math Release, September 27, 2026, result family 293, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.FiniteFactor.exists_source_prepared_finite` of [lean/OAI/Analysis/FiniteFactor/CrossedProduct/PreparedFinite.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FiniteFactor/CrossedProduct/PreparedFinite.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.FiniteFactor`, with `open MeasureTheory Filter`, `open scoped ENNReal Topology`):
--
--   ```lean
--   theorem exists_source_prepared_finite : ∃ θ : SourceCoordinate → ℝ,
--       SourceRationalIndependent θ ∧
--       (∃ j : ℕ, SourceSecondPhasesFrom θ j) ∧
--       SourceOrderedTorusSampling θ ∧
--       (∀ k : ℤ, MeasurePreserving (coordinateRotate θ k) sourceSamplingHaar sourceSamplingHaar) ∧
--       (∀ k : ℤ, k ≠ 0 → ∀ x, coordinateRotate θ k x ≠ x) ∧
--       IsFiniteAlgebra (sourceAlgebra θ) ∧
--       Nonempty (TracialRepresentation (sourceAlgebra θ)) ∧
--       ∃ hθ : SourceAngles θ,
--         let T := sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg
--         T ∈ sourceAlgebra θ ∧ T ≠ 0 ∧ Function.Injective T ∧ ‖T‖ ≤ 1 ∧
--           Tendsto (fun n : ℕ => ‖T^n‖^(1/(n : ℝ))) atTop (𝓝 0)
--   ```
--
--   **Definitions.** The statement is written with `OAI.FiniteFactor.SourceAngles`, `OAI.FiniteFactor.SourceCoordinate`, `OAI.FiniteFactor.SourceHilbert`, `OAI.FiniteFactor.SourceOrderedTorusSampling`, `OAI.FiniteFactor.SourceRationalIndependent`, `OAI.FiniteFactor.SourceSecondPhasesFrom`, `OAI.FiniteFactor.TracialRepresentation`, `OAI.FiniteFactor.coordinateRotate`, `OAI.FiniteFactor.sourceAlgebra`, `OAI.FiniteFactor.sourceBlockSize`, `OAI.FiniteFactor.sourceLogWeight`, `OAI.FiniteFactor.sourceMeasure`, `OAI.FiniteFactor.sourceSamplingHaar` and `OAI.FiniteFactor.SourceAngles.nonneg` (definitions bundle `OAIQ3Ff000` of this split); `OAI.FiniteFactor.sourceLogWeight_nonneg` and `OAI.FiniteFactor.sourceOperator` (definitions bundle `OAIQ3Ff002` of this split); `OAI.FiniteFactor.IsFiniteAlgebra` (the published bundle `Def_FiniteFactor`).
--
--   **Used by.** The proof of `OAI.FiniteFactor.main_theorem` of this split imports it.
-- source:
--   OpenAI, Invariant-projection counterexamples for every irrational rotation, OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 293; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Invariant-projection-counterexamples-for-every-irrational-rotation-September-27-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FiniteFactor/CrossedProduct/PreparedFinite.lean (declaration OAI.FiniteFactor.exists_source_prepared_finite)

import Mathlib
import Definitions.Def_FiniteFactor
import Definitions.Def_OAIQ3Ff002

section

attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal Topology
noncomputable section

theorem exists_source_prepared_finite : ∃ θ : SourceCoordinate → ℝ,
    SourceRationalIndependent θ ∧
    (∃ j : ℕ, SourceSecondPhasesFrom θ j) ∧
    SourceOrderedTorusSampling θ ∧
    (∀ k : ℤ, MeasurePreserving (coordinateRotate θ k) sourceSamplingHaar sourceSamplingHaar) ∧
    (∀ k : ℤ, k ≠ 0 → ∀ x, coordinateRotate θ k x ≠ x) ∧
    IsFiniteAlgebra (sourceAlgebra θ) ∧
    Nonempty (TracialRepresentation (sourceAlgebra θ)) ∧
    ∃ hθ : SourceAngles θ,
      let T := sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg
      T ∈ sourceAlgebra θ ∧ T ≠ 0 ∧ Function.Injective T ∧ ‖T‖ ≤ 1 ∧
        Tendsto (fun n : ℕ => ‖T^n‖^(1/(n : ℝ))) atTop (𝓝 0) := by
  sorry

end
end FiniteFactor

end OAI
end
