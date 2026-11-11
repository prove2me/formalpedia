-- Prove2me | Theorems.Thm_OAI_CriticalPercolation_BondGraph_bondWeight_le_at_end
-- name    : OAI.CriticalPercolation.BondGraph.bondWeight_le_at_end
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T17:17:16.852219+00:00
-- url     : https://prove2.me/theorems/c3f96ad7-52a3-4d1c-b92d-8dcb54d763e9
-- title:
--   OAI.CriticalPercolation.BondGraph.bondWeight_le_at_end: intermediate lemma from OpenAI, No percolation at criticality on quasi-transitive graphs (result family 213)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CriticalPercolation.BondGraph.no_percolation_at_criticality`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *No percolation at criticality on quasi-transitive graphs (result family 213)*, OpenAI Math Release, September 24, 2026, result family 213, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CriticalPercolation.BondGraph.bondWeight_le_at_end` of [lean/OAI/Probability/CriticalPercolation/Modular/ModularIncidence.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Modular/ModularIncidence.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CriticalPercolation.BondGraph`, with `open Set MeasureTheory`, `open scoped Classical ENNReal BigOperators`):
--
--   ```lean
--   lemma bondWeight_le_at_end (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
--       (K : ℕ) (hK : ∀ v, (G.vertexBall v 1).ncard≤K) (o v : V) (e : E)
--       (hv : v∈G.ends e) : G.bondWeight o e ≤ (2*K : ℕ)*G.stabilizerWeight o v
--   ```
--
--   **Definitions.** The statement is written with `OAI.CriticalPercolation.BondGraph.bondWeight`, `OAI.CriticalPercolation.BondGraph.stabilizerWeight` and `OAI.CriticalPercolation.BondGraph.vertexBall` (definitions bundle `OAIQ228B000` of this split); `OAI.CriticalPercolation.BondGraph`, `OAI.CriticalPercolation.BondGraph.LocallyFinite` and `OAI.CriticalPercolation.BondGraph.fullGraph` (the published bundle `Def_CriticalPercolation`).
--
--   **Used by.** The proofs of `OAI.CriticalPercolation.BondGraph.bondWeight_le_of_clusterPeak` and `OAI.CriticalPercolation.BondGraph.weighted_incidence_le` of this split import it.
-- source:
--   OpenAI, No percolation at criticality on quasi-transitive graphs (result family 213), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 213; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/No-percolation-at-criticality-on-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Modular/ModularIncidence.lean (declaration OAI.CriticalPercolation.BondGraph.bondWeight_le_at_end)

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
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma bondWeight_le_at_end (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (K : ℕ) (hK : ∀ v, (G.vertexBall v 1).ncard≤K) (o v : V) (e : E)
    (hv : v∈G.ends e) : G.bondWeight o e ≤ (2*K : ℕ)*G.stabilizerWeight o v := by
  sorry

end CriticalPercolation.BondGraph
end
end

end OAI
end
