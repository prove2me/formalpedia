-- Prove2me | Theorems.Thm_OAI_CriticalPercolation_BondGraph_restriction_incident_subset
-- name    : OAI.CriticalPercolation.BondGraph.restriction_incident_subset
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T17:20:45.088722+00:00
-- url     : https://prove2.me/theorems/1d2ad65f-b810-4784-a9a9-54c59bc8c1b0
-- title:
--   OAI.CriticalPercolation.BondGraph.restriction_incident_subset: intermediate lemma from OpenAI, No percolation at criticality on quasi-transitive graphs (result family 213)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CriticalPercolation.BondGraph.no_percolation_at_criticality`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *No percolation at criticality on quasi-transitive graphs (result family 213)*, OpenAI Math Release, September 24, 2026, result family 213, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CriticalPercolation.BondGraph.restriction_incident_subset` of [lean/OAI/Probability/CriticalPercolation/Modular/WeightedExplorationCost.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Modular/WeightedExplorationCost.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CriticalPercolation.BondGraph`, with `open Set`, `open scoped Classical ENNReal`):
--
--   ```lean
--   lemma restriction_incident_subset (s : Set E) (ω : Set E) (x : V) {e : s}
--       (he : e∈(G.restrictEdges s).incidentEdges ((G.restrictEdges s).cluster (Subtype.val ⁻¹' ω) x)) :
--       e.val∈G.incidentEdges (G.cluster ω x)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CriticalPercolation.BondGraph.incidentEdges` and `OAI.CriticalPercolation.BondGraph.restrictEdges` (definitions bundle `OAIQ228B000` of this split); `OAI.CriticalPercolation.BondGraph` and `OAI.CriticalPercolation.BondGraph.cluster` (the published bundle `Def_CriticalPercolation`).
--
--   **Used by.** The proof of `OAI.CriticalPercolation.BondGraph.restriction_weighted_quadratic_le` of this split imports it.
-- source:
--   OpenAI, No percolation at criticality on quasi-transitive graphs (result family 213), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 213; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/No-percolation-at-criticality-on-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Modular/WeightedExplorationCost.lean (declaration OAI.CriticalPercolation.BondGraph.restriction_incident_subset)

import Mathlib
import Definitions.Def_CriticalPercolation
import Definitions.Def_OAIQ228B000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma restriction_incident_subset (s : Set E) (ω : Set E) (x : V) {e : s}
    (he : e∈(G.restrictEdges s).incidentEdges ((G.restrictEdges s).cluster (Subtype.val ⁻¹' ω) x)) :
    e.val∈G.incidentEdges (G.cluster ω x) := by
  sorry

end CriticalPercolation.BondGraph
end
end

end OAI
end
