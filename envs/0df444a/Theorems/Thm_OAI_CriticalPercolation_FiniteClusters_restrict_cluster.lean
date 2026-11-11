-- Prove2me | Theorems.Thm_OAI_CriticalPercolation_FiniteClusters_restrict_cluster
-- name    : OAI.CriticalPercolation.FiniteClusters.restrict_cluster
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T17:21:51.116649+00:00
-- url     : https://prove2.me/theorems/0f5d0776-86ad-4c28-9178-138aadd5aa0a
-- title:
--   OAI.CriticalPercolation.FiniteClusters.restrict_cluster: intermediate lemma from OpenAI, No percolation at criticality on quasi-transitive graphs (result family 213)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CriticalPercolation.BondGraph.no_percolation_at_criticality`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *No percolation at criticality on quasi-transitive graphs (result family 213)*, OpenAI Math Release, September 24, 2026, result family 213, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CriticalPercolation.FiniteClusters.restrict_cluster` of [lean/OAI/Probability/CriticalPercolation/Modular/ClusterMassRestriction.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Modular/ClusterMassRestriction.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CriticalPercolation.FiniteClusters`, with `open Set MeasureTheory Filter`, `open scoped Classical BigOperators Topology`):
--
--   ```lean
--   lemma restrict_cluster (K : Set E) (ω : Set E) (v : V) :
--       (G.restrictEdges K).cluster (Subtype.val ⁻¹' ω) v = G.cluster (K ∩ ω) v
--   ```
--
--   **Definitions.** The statement is written with `OAI.CriticalPercolation.BondGraph.restrictEdges` (definitions bundle `OAIQ228B000` of this split); `OAI.CriticalPercolation.BondGraph` and `OAI.CriticalPercolation.BondGraph.cluster` (the published bundle `Def_CriticalPercolation`).
--
--   **Used by.** The proofs of `OAI.CriticalPercolation.BondGraph.UnimodularRoot.critical_atMostOneInfinite_ae`, `OAI.CriticalPercolation.BondGraph.expected_discrepancy_peakBand_fourth` and `OAI.CriticalPercolation.BondGraph.restriction_incident_subset` of this split import it.
-- source:
--   OpenAI, No percolation at criticality on quasi-transitive graphs (result family 213), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 213; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/No-percolation-at-criticality-on-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Modular/ClusterMassRestriction.lean (declaration OAI.CriticalPercolation.FiniteClusters.restrict_cluster)

import Mathlib
import Definitions.Def_CriticalPercolation
import Definitions.Def_OAIQ228B000

section

attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical BigOperators Topology

namespace CriticalPercolation.FiniteClusters
variable {V E : Type*} (G : BondGraph V E)

lemma restrict_cluster (K : Set E) (ω : Set E) (v : V) :
    (G.restrictEdges K).cluster (Subtype.val ⁻¹' ω) v = G.cluster (K ∩ ω) v := by
  sorry

end CriticalPercolation.FiniteClusters
end
end

end OAI
end
