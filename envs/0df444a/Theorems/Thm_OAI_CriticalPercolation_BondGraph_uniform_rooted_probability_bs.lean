-- Prove2me | Theorems.Thm_OAI_CriticalPercolation_BondGraph_uniform_rooted_probability_bs
-- name    : OAI.CriticalPercolation.BondGraph.uniform_rooted_probability_bs
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T13:29:23.990326+00:00
-- url     : https://prove2.me/theorems/3f762e4c-9a40-4ef6-b6f5-e860743cea7b
-- title:
--   OAI.CriticalPercolation.BondGraph.uniform_rooted_probability_bs: intermediate lemma from OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Percolation.BenjaminiSchramm.cayley_main`, `OAI.Percolation.BenjaminiSchramm.critical_laws` and `OAI.Percolation.BenjaminiSchramm.full_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)*, OpenAI Math Release, September 24, 2026, result family 214, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CriticalPercolation.BondGraph.uniform_rooted_probability` of [lean/OAI/Probability/CriticalPercolation/GraphGeometry/InfiniteEventSubsetHit.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/GraphGeometry/InfiniteEventSubsetHit.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CriticalPercolation.BondGraph`, with `open scoped BigOperators`, `open scoped Classical ENNReal`, `open Set`, `open Set MeasureTheory ProbabilityTheory Filter`, `open scoped Classical Topology`, `open Set MeasureTheory ProbabilityTheory`, `open scoped Classical`, `open Filter Topology`):
--
--   ```lean
--   theorem uniform_rooted_probability_bs
--       (hconnected : G.fullGraph.Connected) (hlocal : G.LocallyFinite)
--       (hquasi : G.QuasiTransitive) (p : unitInterval)
--       (hp : 0 < G.law p G.percolates) :
--       ∃ θ : ℝ, 0 < θ ∧ ∀ o : V, θ ≤ (G.law p).real (G.infiniteEvent o)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CriticalPercolation.BondGraph`, `OAI.CriticalPercolation.BondGraph.LocallyFinite`, `OAI.CriticalPercolation.BondGraph.QuasiTransitive`, `OAI.CriticalPercolation.BondGraph.fullGraph`, `OAI.CriticalPercolation.BondGraph.infiniteEvent`, `OAI.CriticalPercolation.BondGraph.law` and `OAI.CriticalPercolation.BondGraph.percolates` (definitions bundle `OAIQ078B000` of this split).
--
--   **Used by.** The proofs of `OAI.CriticalPercolation.BondGraph.main_light_or_sparse_polynomial_boundary_bs`, `OAI.CriticalPercolation.BondGraph.uniform_lower_nestedLayer_blocks_bs`, `OAI.CriticalPercolation.BondGraph.unique_cluster_direction_unbounded_ae_bs` and `OAI.CriticalPercolation.Sharpness.critical_null_of_unique_bs` of this split import it.
-- source:
--   OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 214; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-of-percolation-on-nonamenable-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/GraphGeometry/InfiniteEventSubsetHit.lean (declaration OAI.CriticalPercolation.BondGraph.uniform_rooted_probability)

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
open scoped BigOperators
open scoped Classical ENNReal
open Set
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology
open Set MeasureTheory ProbabilityTheory
open scoped Classical
open Filter Topology

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

theorem uniform_rooted_probability_bs
    (hconnected : G.fullGraph.Connected) (hlocal : G.LocallyFinite)
    (hquasi : G.QuasiTransitive) (p : unitInterval)
    (hp : 0 < G.law p G.percolates) :
    ∃ θ : ℝ, 0 < θ ∧ ∀ o : V, θ ≤ (G.law p).real (G.infiniteEvent o) := by
  sorry

end CriticalPercolation.BondGraph
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology Classical

end
end

end OAI
end
