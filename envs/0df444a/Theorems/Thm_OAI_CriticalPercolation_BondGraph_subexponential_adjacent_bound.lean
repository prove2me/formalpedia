-- Prove2me | Theorems.Thm_OAI_CriticalPercolation_BondGraph_subexponential_adjacent_bound
-- name    : OAI.CriticalPercolation.BondGraph.subexponential_adjacent_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T17:22:10.516406+00:00
-- url     : https://prove2.me/theorems/7fb1e439-dc15-4369-9894-bc0331a7b48f
-- title:
--   OAI.CriticalPercolation.BondGraph.subexponential_adjacent_bound: intermediate lemma from OpenAI, No percolation at criticality on quasi-transitive graphs (result family 213)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CriticalPercolation.BondGraph.no_percolation_at_criticality`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *No percolation at criticality on quasi-transitive graphs (result family 213)*, OpenAI Math Release, September 24, 2026, result family 213, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CriticalPercolation.BondGraph.subexponential_adjacent_bound` of [lean/OAI/Probability/CriticalPercolation/GraphGeometry/InfiniteAdjacent.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/GraphGeometry/InfiniteAdjacent.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CriticalPercolation.BondGraph`, with `open Set MeasureTheory ProbabilityTheory Filter`, `open scoped Classical Topology`):
--
--   ```lean
--   theorem subexponential_adjacent_bound (hconnected : G.fullGraph.Connected)
--       (hlocal : G.LocallyFinite) (hquasi : G.QuasiTransitive)
--       (hg : G.SubexponentialGrowth) :
--       ∃ A : ℝ, 0<A ∧ ∀ (p : unitInterval), (p:ℝ)∈Set.Ioo 0 1 → ∀ (e : E) (K : ℕ),
--         (G.law p).real (G.twoClusterEvent (G.ends e).out.1 (G.ends e).out.2 (4^K)) ≤
--           A/((p:ℝ)*(2:ℝ)^K)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CriticalPercolation.BondGraph.SubexponentialGrowth` and `OAI.CriticalPercolation.BondGraph.twoClusterEvent` (definitions bundle `OAIQ228B000` of this split); `OAI.CriticalPercolation.BondGraph`, `OAI.CriticalPercolation.BondGraph.LocallyFinite`, `OAI.CriticalPercolation.BondGraph.QuasiTransitive`, `OAI.CriticalPercolation.BondGraph.fullGraph` and `OAI.CriticalPercolation.BondGraph.law` (the published bundle `Def_CriticalPercolation`).
--
--   **Used by.** The proofs of `OAI.CriticalPercolation.BondGraph.atMostOneInfinite_ae` and `OAI.CriticalPercolation.BondGraph.no_percolation_at_criticality_superpolynomial` of this split import it.
-- source:
--   OpenAI, No percolation at criticality on quasi-transitive graphs (result family 213), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 213; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/No-percolation-at-criticality-on-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/GraphGeometry/InfiniteAdjacent.lean (declaration OAI.CriticalPercolation.BondGraph.subexponential_adjacent_bound)

import Mathlib
import Definitions.Def_CriticalPercolation
import Definitions.Def_OAIQ228B000

section

attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut
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

theorem subexponential_adjacent_bound (hconnected : G.fullGraph.Connected)
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
