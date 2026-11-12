-- Prove2me | Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_JointMaskedSelection_OrbitData_goodEvent_card_lower
-- name    : OAI.MatrixAllFields.MatrixMultiplication.JointMaskedSelection.OrbitData.goodEvent_card_lower
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T11:25:59.765912+00:00
-- url     : https://prove2.me/theorems/03d4770f-6cb7-4db7-8f8c-4ae69135aa09
-- title:
--   OAI.MatrixAllFields.MatrixMultiplication.JointMaskedSelection.OrbitData.goodEvent_card_lower: intermediate lemma from OpenAI, Staggered extraction for exact matrix multiplication over every field
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MatrixAllFields.MatrixMultiplication.AllFieldMain.omega_lt_source_constant`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Staggered extraction for exact matrix multiplication over every field*, OpenAI Math Release, September 24, 2026, result family 107, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MatrixAllFields.MatrixMultiplication.JointMaskedSelection.OrbitData.goodEvent_card_lower` of [lean/OAI/LinearAlgebra/MatrixFields/Extraction/JointMaskedSelection.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/LinearAlgebra/MatrixFields/Extraction/JointMaskedSelection.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MatrixAllFields.MatrixMultiplication.JointMaskedSelection.OrbitData`, with `open scoped BigOperators Topology Polynomial`, `open JointCoarseHashing JointExtractionRates`):
--
--   ```lean
--   theorem goodEvent_card_lower (d : OrbitData P E O V) (k : ℕ)
--       (U : Finset (ZMod (37 ^ k))) (N : ℝ) (hN : 0 < N) (e : E) (D : ℕ)
--       (hdegree : ∀ o ∈ d.orbits e, ∀ v ∈ d.passing e o, (d.competitors e o v).card ≤ D)
--       (hsmall : ((d.eligibilityCompetitors e).card : ℝ) / ((37 ^ k : ℕ) : ℝ) +
--         ((d.orbits e).card : ℝ) * N * ((D : ℝ) / ((37 ^ k : ℕ) : ℝ)) ≤ 1 / 2) :
--       ((U.card : ℝ) / ((37 ^ k : ℕ) : ℝ) ^ 2 / 2) *
--         (Fintype.card (Sample P k) : ℝ) ≤ (d.goodEvent k U N e).card
--   ```
--
--   **Definitions.** The statement is written with `OAI.MatrixAllFields.MatrixMultiplication.JointCoarseHashing.Sample`, `OAI.MatrixAllFields.MatrixMultiplication.JointCoarseHashing.Triple`, `OAI.MatrixAllFields.MatrixMultiplication.JointMaskedSelection.OrbitData`, `OAI.MatrixAllFields.MatrixMultiplication.JointMaskedSelection.OrbitData.eligibilityCompetitors` and `OAI.MatrixAllFields.MatrixMultiplication.JointMaskedSelection.OrbitData.goodEvent` (definitions bundle `OAIQ254M000` of this split).
--
--   **Used by.** The proof of `OAI.MatrixAllFields.MatrixMultiplication.JointMaskedGoodSelection.eventually_exists_good_selection` of this split imports it.
-- source:
--   OpenAI, Staggered extraction for exact matrix multiplication over every field, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 107; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/LinearAlgebra/MatrixFields/Extraction/JointMaskedSelection.lean (declaration OAI.MatrixAllFields.MatrixMultiplication.JointMaskedSelection.OrbitData.goodEvent_card_lower)

import Mathlib
import Definitions.Def_OAIQ254M000

section

attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.aPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.bPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.initialPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section

noncomputable section

namespace MatrixMultiplication.JointMaskedSelection

open JointCoarseHashing JointExtractionRates

attribute [local instance] Classical.propDecidable

variable {P E O V : Type*}

namespace OrbitData

section Finite

variable [Fintype P]

theorem goodEvent_card_lower (d : OrbitData P E O V) (k : ℕ)
    (U : Finset (ZMod (37 ^ k))) (N : ℝ) (hN : 0 < N) (e : E) (D : ℕ)
    (hdegree : ∀ o ∈ d.orbits e, ∀ v ∈ d.passing e o, (d.competitors e o v).card ≤ D)
    (hsmall : ((d.eligibilityCompetitors e).card : ℝ) / ((37 ^ k : ℕ) : ℝ) +
      ((d.orbits e).card : ℝ) * N * ((D : ℝ) / ((37 ^ k : ℕ) : ℝ)) ≤ 1 / 2) :
    ((U.card : ℝ) / ((37 ^ k : ℕ) : ℝ) ^ 2 / 2) *
      (Fintype.card (Sample P k) : ℝ) ≤ (d.goodEvent k U N e).card := by
  sorry

end Finite

end OrbitData

end MatrixMultiplication.JointMaskedSelection

end
end

end MatrixAllFields

end OAI
end
