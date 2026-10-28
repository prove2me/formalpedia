-- Prove2me | Theorems.Thm_OAI_CriticalPercolation_BondGraph_subexponential_adjacent_bound_bs
-- name    : OAI.CriticalPercolation.BondGraph.subexponential_adjacent_bound_bs
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T13:29:25.446395+00:00
-- url     : https://prove2.me/theorems/9de2b515-71f1-41ec-b3e7-128191d93d42
-- title:
--   OAI.CriticalPercolation.BondGraph.subexponential_adjacent_bound_bs: intermediate lemma from OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Percolation.BenjaminiSchramm.cayley_main`, `OAI.Percolation.BenjaminiSchramm.critical_laws` and `OAI.Percolation.BenjaminiSchramm.full_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)*, OpenAI Math Release, September 24, 2026, result family 214, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CriticalPercolation.BondGraph.subexponential_adjacent_bound` of [lean/OAI/Probability/CriticalPercolation/GraphGeometry/InfiniteAdjacent.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/GraphGeometry/InfiniteAdjacent.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CriticalPercolation.BondGraph`, with `open Set MeasureTheory ProbabilityTheory Filter`, `open scoped Classical Topology`):
--
--   ```lean
--   theorem subexponential_adjacent_bound_bs (hconnected : G.fullGraph.Connected)
--       (hlocal : G.LocallyFinite) (hquasi : G.QuasiTransitive)
--       (hg : G.SubexponentialGrowth) :
--       ∃ A : ℝ, 0<A ∧ ∀ (p : unitInterval), (p:ℝ)∈Set.Ioo 0 1 → ∀ (e : E) (K : ℕ),
--         (G.law p).real (G.twoClusterEvent (G.ends e).out.1 (G.ends e).out.2 (4^K)) ≤
--           A/((p:ℝ)*(2:ℝ)^K)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CriticalPercolation.BondGraph`, `OAI.CriticalPercolation.BondGraph.LocallyFinite`, `OAI.CriticalPercolation.BondGraph.QuasiTransitive`, `OAI.CriticalPercolation.BondGraph.SubexponentialGrowth`, `OAI.CriticalPercolation.BondGraph.fullGraph`, `OAI.CriticalPercolation.BondGraph.law` and `OAI.CriticalPercolation.BondGraph.twoClusterEvent` (definitions bundle `OAIQ078B000` of this split).
--
--   **Used by.** The proofs of `OAI.CriticalPercolation.BondGraph.eventually_no_superpolynomial_band_bs` and `OAI.CriticalPercolation.BondGraph.unique_cluster_direction_unbounded_ae_bs` of this split import it.
-- source:
--   OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 214; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-of-percolation-on-nonamenable-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/GraphGeometry/InfiniteAdjacent.lean (declaration OAI.CriticalPercolation.BondGraph.subexponential_adjacent_bound)

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
section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology

namespace CriticalPercolation.BondGraph
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

theorem subexponential_adjacent_bound_bs (hconnected : G.fullGraph.Connected)
    (hlocal : G.LocallyFinite) (hquasi : G.QuasiTransitive)
    (hg : G.SubexponentialGrowth) :
    ∃ A : ℝ, 0<A ∧ ∀ (p : unitInterval), (p:ℝ)∈Set.Ioo 0 1 → ∀ (e : E) (K : ℕ),
      (G.law p).real (G.twoClusterEvent (G.ends e).out.1 (G.ends e).out.2 (4^K)) ≤
        A/((p:ℝ)*(2:ℝ)^K) := by
  sorry

end CriticalPercolation.BondGraph
end
end
end

end OAI
end
