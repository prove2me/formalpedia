-- Prove2me | Theorems.Thm_OAI_CriticalPercolation_BondGraph_cluster_mono
-- name    : OAI.CriticalPercolation.BondGraph.cluster_mono
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T17:14:34.485586+00:00
-- url     : https://prove2.me/theorems/2036a591-36b0-4c1e-8e9c-b51aad57153b
-- title:
--   OAI.CriticalPercolation.BondGraph.cluster_mono: intermediate lemma from OpenAI, No percolation at criticality on quasi-transitive graphs (result family 213)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CriticalPercolation.BondGraph.no_percolation_at_criticality`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *No percolation at criticality on quasi-transitive graphs (result family 213)*, OpenAI Math Release, September 24, 2026, result family 213, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CriticalPercolation.BondGraph.cluster_mono` of [lean/OAI/Probability/CriticalPercolation/GraphGeometry/VertexBall.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/GraphGeometry/VertexBall.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CriticalPercolation.BondGraph`, with `open Set MeasureTheory ProbabilityTheory`):
--
--   ```lean
--   theorem cluster_mono {ω ω' : Set E} (h : ω ⊆ ω') (v : V) :
--       G.cluster ω v ⊆ G.cluster ω' v
--   ```
--
--   **Definitions.** The statement is written with `OAI.CriticalPercolation.BondGraph` and `OAI.CriticalPercolation.BondGraph.cluster` (the published bundle `Def_CriticalPercolation`).
--
--   **Used by.** The proofs of `OAI.CriticalPercolation.BondGraph.UnimodularRoot.critical_atMostOneInfinite_ae`, `OAI.CriticalPercolation.BondGraph.approximate_moves_contradiction`, `OAI.CriticalPercolation.BondGraph.atMostOneHeavy_critical_ae`, `OAI.CriticalPercolation.BondGraph.atMostOneInfinite_ae`, `OAI.CriticalPercolation.BondGraph.criticalProbability_pos`, `OAI.CriticalPercolation.BondGraph.critical_null_of_compact_open_orbital_quotient`, `OAI.CriticalPercolation.BondGraph.critical_strip_null`, `OAI.CriticalPercolation.BondGraph.expected_discrepancy_peakBand_fourth`, `OAI.CriticalPercolation.BondGraph.fresh_collar_transfer`, `OAI.CriticalPercolation.BondGraph.main_all_light_or_sparse_boundary`, `OAI.CriticalPercolation.BondGraph.main_failure_sparse_polynomial`, `OAI.CriticalPercolation.BondGraph.no_percolation_at_criticality_superpolynomial`, `OAI.CriticalPercolation.BondGraph.restriction_incident_subset`, `OAI.CriticalPercolation.BondGraph.root_corridor_miss`, `OAI.CriticalPercolation.BondGraph.subexponential_adjacent_bound`, `OAI.CriticalPercolation.BondGraph.tendsto_expected_heavy_peakReturn`, `OAI.CriticalPercolation.BondGraph.tendsto_expected_signed_discrepancy_law`, `OAI.CriticalPercolation.BondGraph.uniform_lower_nestedLayer_blocks`, `OAI.CriticalPercolation.Corridor.CoordinateData.prospective_estimate` and `OAI.CriticalPercolation.IncidenceSearch.compile_terminal` of this split import it.
-- source:
--   OpenAI, No percolation at criticality on quasi-transitive graphs (result family 213), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 213; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/No-percolation-at-criticality-on-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/GraphGeometry/VertexBall.lean (declaration OAI.CriticalPercolation.BondGraph.cluster_mono)

import Mathlib
import Definitions.Def_CriticalPercolation

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory

namespace CriticalPercolation
namespace BondGraph
variable {V E : Type*} (G : BondGraph V E)

theorem cluster_mono {ω ω' : Set E} (h : ω ⊆ ω') (v : V) :
    G.cluster ω v ⊆ G.cluster ω' v := by
  sorry

end BondGraph

end CriticalPercolation

open scoped BigOperators
open Set

end
end

end OAI
end
