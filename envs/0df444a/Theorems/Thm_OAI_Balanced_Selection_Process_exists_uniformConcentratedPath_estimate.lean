-- Prove2me | Theorems.Thm_OAI_Balanced_Selection_Process_exists_uniformConcentratedPath_estimate
-- name    : OAI.Balanced.Selection.Process.exists_uniformConcentratedPath_estimate
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T00:05:55.703259+00:00
-- url     : https://prove2.me/theorems/0dcab709-6c76-4e24-ba14-727c3af263cd
-- title:
--   OAI.Balanced.Selection.Process.exists_uniformConcentratedPath_estimate: intermediate lemma from OpenAI, Balanced counterexamples to Ryser's conjecture at prime orders (result family 162)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Balanced.main_result`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Balanced counterexamples to Ryser's conjecture at prime orders (result family 162)*, OpenAI Math Release, September 27, 2026, result family 162, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Balanced.Selection.Process.exists_uniformConcentratedPath_estimate` of [lean/OAI/Combinatorics/BalancedRyser/Selection/SelectionConcentrationUniform.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/BalancedRyser/Selection/SelectionConcentrationUniform.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Balanced.Selection.Process`, with `open Filter MeasureTheory`, `open scoped Topology`):
--
--   ```lean
--   theorem exists_uniformConcentratedPath_estimate (p : Parameters) (hp : p.Admissible) :
--       ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
--         ∀ᶠ q : ℕ in atTop,
--           ∀ (I : Type u) (V : Type v) [Fintype I] [Fintype V],
--           ∀ G : Input I V, GraphBounds G q p.c p.C →
--             (snapshotPathLaw p q G).real {ω | ¬ FirstAbort.ConcentratedPath p q G
--               (p.lastMainTime q (Fintype.card I)) ω} ≤ ε q
--   ```
--
--   **Definitions.** The statement is written with `OAI.Balanced.FiniteHistory.Path`, `OAI.Balanced.Selection.GraphBounds`, `OAI.Balanced.Selection.Input`, `OAI.Balanced.Selection.Process.Parameters`, `OAI.Balanced.Selection.Process.Snapshot`, `OAI.Balanced.Selection.Process.snapshotMeasurableSpace`, `OAI.Balanced.Selection.Process.snapshotPathLaw`, `OAI.Balanced.Selection.Process.FirstAbort.ConcentratedPath`, `OAI.Balanced.Selection.Process.Parameters.Admissible` and `OAI.Balanced.Selection.Process.Parameters.lastMainTime` (definitions bundle `OAIQ63Br001` of this split).
--
--   **Used by.** The proof of `OAI.Balanced.deletion_domination` of this split imports it.
-- source:
--   OpenAI, Balanced counterexamples to Ryser's conjecture at prime orders (result family 162), OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 162; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Balanced-Counterexamples-to-Rysers-Conjecture-at-Prime-Orders-September-27-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/BalancedRyser/Selection/SelectionConcentrationUniform.lean (declaration OAI.Balanced.Selection.Process.exists_uniformConcentratedPath_estimate)

import Mathlib
import Definitions.Def_OAIQ63Br001

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
attribute [local instance] Classical.propDecidable

theorem exists_uniformConcentratedPath_estimate (p : Parameters) (hp : p.Admissible) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∀ᶠ q : ℕ in atTop,
        ∀ (I : Type u) (V : Type v) [Fintype I] [Fintype V],
        ∀ G : Input I V, GraphBounds G q p.c p.C →
          (snapshotPathLaw p q G).real {ω | ¬ FirstAbort.ConcentratedPath p q G
            (p.lastMainTime q (Fintype.card I)) ω} ≤ ε q := by
  sorry
end Balanced.Selection.Process

end

end OAI
end
