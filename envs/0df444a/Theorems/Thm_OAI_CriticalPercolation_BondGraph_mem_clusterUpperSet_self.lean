-- Prove2me | Theorems.Thm_OAI_CriticalPercolation_BondGraph_mem_clusterUpperSet_self
-- name    : OAI.CriticalPercolation.BondGraph.mem_clusterUpperSet_self
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T17:20:20.247905+00:00
-- url     : https://prove2.me/theorems/051c3ca2-0ef4-45dd-9e51-7ce5f74fc285
-- title:
--   OAI.CriticalPercolation.BondGraph.mem_clusterUpperSet_self: intermediate lemma from OpenAI, No percolation at criticality on quasi-transitive graphs (result family 213)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CriticalPercolation.BondGraph.no_percolation_at_criticality`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *No percolation at criticality on quasi-transitive graphs (result family 213)*, OpenAI Math Release, September 24, 2026, result family 213, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CriticalPercolation.BondGraph.mem_clusterUpperSet_self` of [lean/OAI/Probability/CriticalPercolation/Modular/ModularSuperlevels.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Modular/ModularSuperlevels.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CriticalPercolation.BondGraph`, with `open Set MeasureTheory`, `open scoped Classical ENNReal`):
--
--   ```lean
--   lemma mem_clusterUpperSet_self (ω : Set E) (v : V) : v∈G.clusterUpperSet ω v
--   ```
--
--   **Definitions.** The statement is written with `OAI.CriticalPercolation.BondGraph.clusterUpperSet` (definitions bundle `OAIQ228B000` of this split); `OAI.CriticalPercolation.BondGraph` (the published bundle `Def_CriticalPercolation`).
--
--   **Used by.** The proof of `OAI.CriticalPercolation.BondGraph.finite_clusterUpperSet_has_peak` of this split imports it.
-- source:
--   OpenAI, No percolation at criticality on quasi-transitive graphs (result family 213), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 213; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/No-percolation-at-criticality-on-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Modular/ModularSuperlevels.lean (declaration OAI.CriticalPercolation.BondGraph.mem_clusterUpperSet_self)

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
open Set MeasureTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma mem_clusterUpperSet_self (ω : Set E) (v : V) : v∈G.clusterUpperSet ω v := by
  sorry

end CriticalPercolation.BondGraph
end
end

end OAI
end
