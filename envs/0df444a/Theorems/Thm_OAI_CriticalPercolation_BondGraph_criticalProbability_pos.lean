-- Prove2me | Theorems.Thm_OAI_CriticalPercolation_BondGraph_criticalProbability_pos
-- name    : OAI.CriticalPercolation.BondGraph.criticalProbability_pos
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T17:14:30.769238+00:00
-- url     : https://prove2.me/theorems/4f82cf7e-b7c6-4242-8f1d-88194f3c6c17
-- title:
--   OAI.CriticalPercolation.BondGraph.criticalProbability_pos: intermediate lemma from OpenAI, No percolation at criticality on quasi-transitive graphs (result family 213)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CriticalPercolation.BondGraph.no_percolation_at_criticality`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *No percolation at criticality on quasi-transitive graphs (result family 213)*, OpenAI Math Release, September 24, 2026, result family 213, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CriticalPercolation.BondGraph.criticalProbability_pos` of [lean/OAI/Probability/CriticalPercolation/Criticality/PositiveCritical.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Criticality/PositiveCritical.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CriticalPercolation.BondGraph`, with `open Set MeasureTheory ProbabilityTheory Filter`, `open scoped Classical Topology`):
--
--   ```lean
--   theorem criticalProbability_pos (hconnected : G.fullGraph.Connected)
--       (hlocal : G.LocallyFinite) (hquasi : G.QuasiTransitive) :
--       (0:ℝ)<G.criticalProbability
--   ```
--
--   **Definitions.** The statement is written with `OAI.CriticalPercolation.BondGraph`, `OAI.CriticalPercolation.BondGraph.LocallyFinite`, `OAI.CriticalPercolation.BondGraph.QuasiTransitive`, `OAI.CriticalPercolation.BondGraph.criticalProbability` and `OAI.CriticalPercolation.BondGraph.fullGraph` (the published bundle `Def_CriticalPercolation`).
--
--   **Used by.** The proofs of `OAI.CriticalPercolation.BondGraph.UnimodularRoot.critical_atMostOneInfinite_ae`, `OAI.CriticalPercolation.BondGraph.critical_null_of_compact_open_orbital_quotient`, `OAI.CriticalPercolation.BondGraph.critical_strip_null`, `OAI.CriticalPercolation.BondGraph.main_failure_sparse_polynomial` and `OAI.CriticalPercolation.BondGraph.no_percolation_at_criticality_superpolynomial` of this split import it.
-- source:
--   OpenAI, No percolation at criticality on quasi-transitive graphs (result family 213), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 213; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/No-percolation-at-criticality-on-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Criticality/PositiveCritical.lean (declaration OAI.CriticalPercolation.BondGraph.criticalProbability_pos)

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
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

theorem criticalProbability_pos (hconnected : G.fullGraph.Connected)
    (hlocal : G.LocallyFinite) (hquasi : G.QuasiTransitive) :
    (0:ℝ)<G.criticalProbability := by
  sorry

end CriticalPercolation.BondGraph
end
end
end

end OAI
end
