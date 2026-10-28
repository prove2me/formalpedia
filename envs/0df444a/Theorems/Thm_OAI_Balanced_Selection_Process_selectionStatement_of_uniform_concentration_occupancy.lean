-- Prove2me | Theorems.Thm_OAI_Balanced_Selection_Process_selectionStatement_of_uniform_concentration_occupancy
-- name    : OAI.Balanced.Selection.Process.selectionStatement_of_uniform_concentration_occupancy
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T00:14:17.418708+00:00
-- url     : https://prove2.me/theorems/39f39e72-5882-44dd-9805-1df5f997abb8
-- title:
--   OAI.Balanced.Selection.Process.selectionStatement_of_uniform_concentration_occupancy: intermediate lemma from OpenAI, Balanced counterexamples to Ryser's conjecture at prime orders (result family 162)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Balanced.main_result`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Balanced counterexamples to Ryser's conjecture at prime orders (result family 162)*, OpenAI Math Release, September 27, 2026, result family 162, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Balanced.Selection.Process.selectionStatement_of_uniform_concentration_occupancy` of [lean/OAI/Combinatorics/BalancedRyser/Selection/SelectionSuccessUniform.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/BalancedRyser/Selection/SelectionSuccessUniform.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Balanced.Selection.Process`, with `open Filter MeasureTheory`, `open scoped Topology`):
--
--   ```lean
--   theorem selectionStatement_of_uniform_concentration_occupancy
--       (hconcentration : ∀ p : Parameters, p.Admissible →
--         ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
--           ∀ᶠ q : ℕ in atTop, UniformConcentrationEstimate.{u,v} p ε q)
--       (hoccupancy : ∀ p : Parameters, p.Admissible →
--         ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
--           ∀ᶠ q : ℕ in atTop, UniformOccupancyEstimate.{u,v,w} p ε q) :
--       SelectionStatement.{u,v,w}
--   ```
--
--   **Definitions.** The statement is written with `OAI.Balanced.SelectionStatement`, `OAI.Balanced.Selection.Process.Parameters` and `OAI.Balanced.Selection.Process.Parameters.Admissible` (definitions bundle `OAIQ63Br001` of this split); `OAI.Balanced.Selection.Process.UniformConcentrationEstimate` and `OAI.Balanced.Selection.Process.UniformOccupancyEstimate` (definitions bundle `OAIQ63Br004` of this split).
--
--   **Used by.** The proof of `OAI.Balanced.deletion_domination` of this split imports it.
-- source:
--   OpenAI, Balanced counterexamples to Ryser's conjecture at prime orders (result family 162), OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 162; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Balanced-Counterexamples-to-Rysers-Conjecture-at-Prime-Orders-September-27-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/BalancedRyser/Selection/SelectionSuccessUniform.lean (declaration OAI.Balanced.Selection.Process.selectionStatement_of_uniform_concentration_occupancy)

import Mathlib
import Definitions.Def_OAIQ63Br004

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter MeasureTheory
open scoped Topology

namespace Balanced.Selection.Process

universe u v w

theorem selectionStatement_of_uniform_concentration_occupancy
    (hconcentration : ∀ p : Parameters, p.Admissible →
      ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
        ∀ᶠ q : ℕ in atTop, UniformConcentrationEstimate.{u,v} p ε q)
    (hoccupancy : ∀ p : Parameters, p.Admissible →
      ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
        ∀ᶠ q : ℕ in atTop, UniformOccupancyEstimate.{u,v,w} p ε q) :
    SelectionStatement.{u,v,w} := by
  sorry

end Balanced.Selection.Process

end

end OAI
end
