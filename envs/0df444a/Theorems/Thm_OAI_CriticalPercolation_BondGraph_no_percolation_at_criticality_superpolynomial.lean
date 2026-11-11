-- Prove2me | Theorems.Thm_OAI_CriticalPercolation_BondGraph_no_percolation_at_criticality_superpolynomial
-- name    : OAI.CriticalPercolation.BondGraph.no_percolation_at_criticality_superpolynomial
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T17:20:34.08529+00:00
-- url     : https://prove2.me/theorems/53ba6614-91c8-4150-b025-46ffaedbf064
-- title:
--   OAI.CriticalPercolation.BondGraph.no_percolation_at_criticality_superpolynomial: intermediate lemma from OpenAI, No percolation at criticality on quasi-transitive graphs (result family 213)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CriticalPercolation.BondGraph.no_percolation_at_criticality`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *No percolation at criticality on quasi-transitive graphs (result family 213)*, OpenAI Math Release, September 24, 2026, result family 213, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CriticalPercolation.BondGraph.no_percolation_at_criticality_superpolynomial` of [lean/OAI/Probability/CriticalPercolation/Growth/SuperpolynomialMain.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Growth/SuperpolynomialMain.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CriticalPercolation.BondGraph`, with `open Set MeasureTheory ProbabilityTheory Filter`, `open scoped Classical Topology`):
--
--   ```lean
--   theorem no_percolation_at_criticality_superpolynomial
--       (hconnected : G.fullGraph.Connected) (hlocal : G.LocallyFinite)
--       (hquasi : G.QuasiTransitive) (hpc : G.criticalProbability<1)
--       (hsub : G.SubexponentialGrowth) (hsuper : G.SuperpolynomialGrowth) :
--       G.law G.criticalProbability G.percolates = 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.CriticalPercolation.BondGraph.SubexponentialGrowth` and `OAI.CriticalPercolation.BondGraph.SuperpolynomialGrowth` (definitions bundle `OAIQ228B000` of this split); `OAI.CriticalPercolation.BondGraph`, `OAI.CriticalPercolation.BondGraph.LocallyFinite`, `OAI.CriticalPercolation.BondGraph.QuasiTransitive`, `OAI.CriticalPercolation.BondGraph.criticalProbability`, `OAI.CriticalPercolation.BondGraph.fullGraph`, `OAI.CriticalPercolation.BondGraph.law` and `OAI.CriticalPercolation.BondGraph.percolates` (the published bundle `Def_CriticalPercolation`).
--
--   **Used by.** The proof of `OAI.CriticalPercolation.BondGraph.main_all_light_or_sparse_boundary` of this split imports it.
-- source:
--   OpenAI, No percolation at criticality on quasi-transitive graphs (result family 213), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 213; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/No-percolation-at-criticality-on-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Growth/SuperpolynomialMain.lean (declaration OAI.CriticalPercolation.BondGraph.no_percolation_at_criticality_superpolynomial)

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
variable {V E : Type*} (G : BondGraph V E)

theorem no_percolation_at_criticality_superpolynomial
    (hconnected : G.fullGraph.Connected) (hlocal : G.LocallyFinite)
    (hquasi : G.QuasiTransitive) (hpc : G.criticalProbability<1)
    (hsub : G.SubexponentialGrowth) (hsuper : G.SuperpolynomialGrowth) :
    G.law G.criticalProbability G.percolates = 0 := by
  sorry

end CriticalPercolation.BondGraph
end
end
end

end OAI
end
