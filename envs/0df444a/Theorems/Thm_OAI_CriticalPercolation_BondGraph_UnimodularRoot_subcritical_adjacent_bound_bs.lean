-- Prove2me | Theorems.Thm_OAI_CriticalPercolation_BondGraph_UnimodularRoot_subcritical_adjacent_bound_bs
-- name    : OAI.CriticalPercolation.BondGraph.UnimodularRoot.subcritical_adjacent_bound_bs
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T13:20:57.222443+00:00
-- url     : https://prove2.me/theorems/881a2874-e014-4198-9ae7-75a34616678e
-- title:
--   OAI.CriticalPercolation.BondGraph.UnimodularRoot.subcritical_adjacent_bound_bs: intermediate lemma from OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Percolation.BenjaminiSchramm.cayley_main`, `OAI.Percolation.BenjaminiSchramm.critical_laws` and `OAI.Percolation.BenjaminiSchramm.full_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)*, OpenAI Math Release, September 24, 2026, result family 214, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CriticalPercolation.BondGraph.UnimodularRoot.subcritical_adjacent_bound` of [lean/OAI/Probability/CriticalPercolation/Modular/UnimodularAdjacent.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Modular/UnimodularAdjacent.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CriticalPercolation.BondGraph`, with `open Set MeasureTheory Filter`, `open scoped Classical BigOperators Topology`):
--
--   ```lean
--   theorem UnimodularRoot.subcritical_adjacent_bound_bs (R : G.UnimodularRoot)
--       (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (e : E) :
--       ∃ A : ℝ, 0 < A ∧ ∀ (p : unitInterval), (p:ℝ) ∈ Ioo 0 1 → p < G.criticalProbability →
--         ∀ k : ℕ, (G.law p).real (G.twoClusterEvent (G.ends e).out.1 (G.ends e).out.2 (4^k)) ≤
--           A/((p:ℝ)*(2:ℝ)^k)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CriticalPercolation.BondGraph`, `OAI.CriticalPercolation.BondGraph.LocallyFinite`, `OAI.CriticalPercolation.BondGraph.UnimodularRoot`, `OAI.CriticalPercolation.BondGraph.criticalProbability`, `OAI.CriticalPercolation.BondGraph.fullGraph`, `OAI.CriticalPercolation.BondGraph.law` and `OAI.CriticalPercolation.BondGraph.twoClusterEvent` (definitions bundle `OAIQ078B000` of this split).
--
--   **Used by.** The proof of `OAI.CriticalPercolation.BondGraph.CombinatoriallyUnimodular.exponential_critical_null_bs` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 214; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-of-percolation-on-nonamenable-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Modular/UnimodularAdjacent.lean (declaration OAI.CriticalPercolation.BondGraph.UnimodularRoot.subcritical_adjacent_bound)

import Mathlib
import Definitions.Def_OAIQ078B000

section

attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical BigOperators Topology

namespace CriticalPercolation.BondGraph
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

theorem UnimodularRoot.subcritical_adjacent_bound_bs (R : G.UnimodularRoot)
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (e : E) :
    ∃ A : ℝ, 0 < A ∧ ∀ (p : unitInterval), (p:ℝ) ∈ Ioo 0 1 → p < G.criticalProbability →
      ∀ k : ℕ, (G.law p).real (G.twoClusterEvent (G.ends e).out.1 (G.ends e).out.2 (4^k)) ≤
        A/((p:ℝ)*(2:ℝ)^k) := by
  sorry

end CriticalPercolation.BondGraph
end
end

end OAI
end
