-- Prove2me | Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_JointOrdinaryPopulationSelection_uniformDegree_log_upper_of_word_support
-- name    : OAI.MatrixAllFields.MatrixMultiplication.JointOrdinaryPopulationSelection.uniformDegree_log_upper_of_word_support
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T05:54:34.047597+00:00
-- url     : https://prove2.me/theorems/89dd4694-c5bb-45f8-9c0d-ce5f8eb54a5d
-- title:
--   OAI.MatrixAllFields.MatrixMultiplication.JointOrdinaryPopulationSelection.uniformDegree_log_upper_of_word_support (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MatrixAllFields.MatrixMultiplication.AllFieldMain.omega_lt_source_constant`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Staggered extraction for exact matrix multiplication over every field*, OpenAI Math Release, September 24, 2026, result family 107, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MatrixAllFields.MatrixMultiplication.JointOrdinaryPopulationSelection.uniformDegree_log_upper_of_word_support` of [lean/OAI/LinearAlgebra/MatrixFields/Parameters/JointOrdinaryPopulationSelection.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/LinearAlgebra/MatrixFields/Parameters/JointOrdinaryPopulationSelection.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MatrixAllFields.MatrixMultiplication.JointOrdinaryPopulationSelection`, with `open scoped BigOperators Topology Polynomial`, `open MatrixMultiplication.Foundation JointPopulation JointPopulationRates Filter`, `open scoped BigOperators Topology`):
--
--   ```lean
--   theorem uniformDegree_log_upper_of_word_support
--       (counts : ℕ → Hist → Shape → ℕ) (sum : Hist → ℕ) (mass : Hist → ℝ)
--       (p : Hist → FiniteLaw Shape) (u v w : Hist → Fin 17 → ℝ) (c : Hist → ℝ)
--       (hmass : ∀ h, 0 ≤ mass h)
--       (hsupport : ∀ᶠ N in atTop, ∀ h word,
--         JointAmbientDegree.localAllowed (counts N) sum h word →
--           ∀ i, 0 < (p h).mass (word i))
--       (hlog : ∀ h a, 0 < (p h).mass a → Real.log ((p h).mass a) =
--         u h (shapeSide 0 a) + v h (shapeSide 1 a) + w h (shapeSide 2 a) - c h)
--       (hcounts : ∀ h a, Tendsto (fun N : ℕ => (counts N h a : ℝ) / (N : ℝ))
--         atTop (𝓝 (mass h * (p h).mass a)))
--       (η : ℝ) (hη : 0 < η) :
--       ∀ᶠ N in atTop, Real.log (uniformDegree (counts N) sum : ℝ) / (N : ℝ) ≤
--         degreeRate mass p + η
--   ```
--
--   **Definitions.** The statement is written with `OAI.MatrixAllFields.MatrixMultiplication.Foundation.FiniteLaw`, `OAI.MatrixAllFields.MatrixMultiplication.JointOrdinaryPopulationSelection.degreeRate`, `OAI.MatrixAllFields.MatrixMultiplication.JointPopulation.Positions`, `OAI.MatrixAllFields.MatrixMultiplication.JointPopulation.Shape` and `OAI.MatrixAllFields.MatrixMultiplication.JointPopulation.shapeSide` (definitions bundle `OAIQ254M000` of this split); `OAI.MatrixAllFields.MatrixMultiplication.JointAmbientDegree.localAllowed` and `OAI.MatrixAllFields.MatrixMultiplication.JointOrdinaryPopulationSelection.uniformDegree` (definitions bundle `OAIQ254M003` of this split).
--
--   **Used by.** The proof of `OAI.MatrixAllFields.MatrixMultiplication.JointOrdinaryPopulationSelection.eventually_exists_selection_of_word_support` of this split imports it.
-- source:
--   OpenAI, Staggered extraction for exact matrix multiplication over every field, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 107; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/LinearAlgebra/MatrixFields/Parameters/JointOrdinaryPopulationSelection.lean (declaration OAI.MatrixAllFields.MatrixMultiplication.JointOrdinaryPopulationSelection.uniformDegree_log_upper_of_word_support)

import Mathlib
import Definitions.Def_OAIQ254M003

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section

noncomputable section

namespace MatrixMultiplication.JointOrdinaryPopulationSelection

open MatrixMultiplication.Foundation JointPopulation JointPopulationRates Filter
open scoped BigOperators Topology

attribute [local instance] Classical.propDecidable

variable {Hist : Type*} [Fintype Hist] [DecidableEq Hist]

theorem uniformDegree_log_upper_of_word_support
    (counts : ℕ → Hist → Shape → ℕ) (sum : Hist → ℕ) (mass : Hist → ℝ)
    (p : Hist → FiniteLaw Shape) (u v w : Hist → Fin 17 → ℝ) (c : Hist → ℝ)
    (hmass : ∀ h, 0 ≤ mass h)
    (hsupport : ∀ᶠ N in atTop, ∀ h word,
      JointAmbientDegree.localAllowed (counts N) sum h word →
        ∀ i, 0 < (p h).mass (word i))
    (hlog : ∀ h a, 0 < (p h).mass a → Real.log ((p h).mass a) =
      u h (shapeSide 0 a) + v h (shapeSide 1 a) + w h (shapeSide 2 a) - c h)
    (hcounts : ∀ h a, Tendsto (fun N : ℕ => (counts N h a : ℝ) / (N : ℝ))
      atTop (𝓝 (mass h * (p h).mass a)))
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ N in atTop, Real.log (uniformDegree (counts N) sum : ℝ) / (N : ℝ) ≤
      degreeRate mass p + η := by
  sorry

end MatrixMultiplication.JointOrdinaryPopulationSelection

end
end

end MatrixAllFields

end OAI
end
