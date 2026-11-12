-- Prove2me | Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldGroupDegreeLaws_eventually_eligibility_card_le
-- name    : OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupDegreeLaws.eventually_eligibility_card_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T08:48:00.062195+00:00
-- url     : https://prove2.me/theorems/095636ef-c04c-4105-8701-13500576fc96
-- title:
--   OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupDegreeLaws.eventually_eligibility_card_le: intermediate lemma from OpenAI, Staggered extraction for exact matrix multiplication over every field
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MatrixAllFields.MatrixMultiplication.AllFieldMain.omega_lt_source_constant`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Staggered extraction for exact matrix multiplication over every field*, OpenAI Math Release, September 24, 2026, result family 107, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupDegreeLaws.eventually_eligibility_card_le` of [lean/OAI/LinearAlgebra/MatrixFields/Entropy/GroupCountRate.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/LinearAlgebra/MatrixFields/Entropy/GroupCountRate.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupDegreeLaws`, with `open scoped BigOperators Topology Polynomial`, `open AllFieldHistory AllFieldHistorySupport AllFieldHistoryChildLaws`, `open AllFieldGroupOrbitData AllFieldGroupNativeLaws`, `open JointPopulation JointCanonicalization MatrixMultiplication.Foundation Filter`, `open scoped BigOperators Topology`):
--
--   ```lean
--   theorem eventually_eligibility_card_le (allocation : Allocation) (sigma : Placement)
--       (width : ℝ) {δ : ℝ} (hδ : 0 < δ) :
--       ∀ᶠ m : ℕ in atTop, ∀ e : Targets (K := K) (tick := tick) allocation m sigma,
--         (((data allocation m width sigma).eligibilityCompetitors e).card : ℝ) ≤
--           Real.exp ((m : ℝ) *
--             (AllFieldActiveCapacity.orderNativeDegree (K := K) (tick := tick) allocation sigma 0 + δ))
--   ```
--
--   **Definitions.** The statement is written with `OAI.MatrixAllFields.MatrixMultiplication.AllFieldActiveCapacity.orderNativeDegree`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitData.Orbit`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitData.Pos`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitData.Targets`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitData.Variable`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.Allocation`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.Placement`, `OAI.MatrixAllFields.MatrixMultiplication.JointCoarseHashing.Triple` and `OAI.MatrixAllFields.MatrixMultiplication.JointMaskedSelection.OrbitData.eligibilityCompetitors` (definitions bundle `OAIQ254M000` of this split); `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitData.data` (definitions bundle `OAIQ254M002` of this split).
--
--   **Used by.** The proof of `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupNativeDegreeBound.exists_threshold_eventually_counts_le` of this split imports it.
-- source:
--   OpenAI, Staggered extraction for exact matrix multiplication over every field, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 107; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/LinearAlgebra/MatrixFields/Entropy/GroupCountRate.lean (declaration OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupDegreeLaws.eventually_eligibility_card_le)

import Mathlib
import Definitions.Def_OAIQ254M002

section

attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIteration.labelsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalRates.zeroWordsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldGroupDegreeLaws

open AllFieldHistory AllFieldHistorySupport AllFieldHistoryChildLaws
open AllFieldGroupOrbitData AllFieldGroupNativeLaws
open JointPopulation JointCanonicalization MatrixMultiplication.Foundation Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ}

theorem eventually_eligibility_card_le (allocation : Allocation) (sigma : Placement)
    (width : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ m : ℕ in atTop, ∀ e : Targets (K := K) (tick := tick) allocation m sigma,
      (((data allocation m width sigma).eligibilityCompetitors e).card : ℝ) ≤
        Real.exp ((m : ℝ) *
          (AllFieldActiveCapacity.orderNativeDegree (K := K) (tick := tick) allocation sigma 0 + δ)) := by
  sorry

end MatrixMultiplication.AllFieldGroupDegreeLaws

end
end

end MatrixAllFields

end OAI
end
