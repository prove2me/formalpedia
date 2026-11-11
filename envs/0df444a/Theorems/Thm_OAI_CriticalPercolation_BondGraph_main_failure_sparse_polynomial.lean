-- Prove2me | Theorems.Thm_OAI_CriticalPercolation_BondGraph_main_failure_sparse_polynomial
-- name    : OAI.CriticalPercolation.BondGraph.main_failure_sparse_polynomial
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T17:19:58.24774+00:00
-- url     : https://prove2.me/theorems/bcba638e-bc11-44d4-b9e1-9819a5886117
-- title:
--   OAI.CriticalPercolation.BondGraph.main_failure_sparse_polynomial: intermediate lemma from OpenAI, No percolation at criticality on quasi-transitive graphs (result family 213)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CriticalPercolation.BondGraph.no_percolation_at_criticality`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *No percolation at criticality on quasi-transitive graphs (result family 213)*, OpenAI Math Release, September 24, 2026, result family 213, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CriticalPercolation.BondGraph.main_failure_sparse_polynomial` of [lean/OAI/Probability/CriticalPercolation/Criticality/MainSparseBoundary.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Criticality/MainSparseBoundary.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CriticalPercolation.BondGraph`, with `open Set MeasureTheory`, `open scoped Classical ENNReal`):
--
--   ```lean
--   theorem main_failure_sparse_polynomial [Infinite V]
--       (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
--       (hpc : G.criticalProbability<1)
--       (hper : G.law G.criticalProbability G.percolates≠0) :
--       G.SubexponentialGrowth ∧ G.CombinatoriallyUnimodular ∧
--         ∃ d : ℕ, 2≤d ∧ ∀ R : ℕ, ∃ n≥R, ∃ v : V, (G.vertexBall v n).ncard≤n^d
--   ```
--
--   **Definitions.** The statement is written with `OAI.CriticalPercolation.BondGraph.CombinatoriallyUnimodular`, `OAI.CriticalPercolation.BondGraph.SubexponentialGrowth` and `OAI.CriticalPercolation.BondGraph.vertexBall` (definitions bundle `OAIQ228B000` of this split); `OAI.CriticalPercolation.BondGraph`, `OAI.CriticalPercolation.BondGraph.LocallyFinite`, `OAI.CriticalPercolation.BondGraph.QuasiTransitive`, `OAI.CriticalPercolation.BondGraph.criticalProbability`, `OAI.CriticalPercolation.BondGraph.fullGraph`, `OAI.CriticalPercolation.BondGraph.law` and `OAI.CriticalPercolation.BondGraph.percolates` (the published bundle `Def_CriticalPercolation`).
--
--   **Used by.** The proof of `OAI.CriticalPercolation.BondGraph.no_percolation_at_criticality` of this split imports it.
-- source:
--   OpenAI, No percolation at criticality on quasi-transitive graphs (result family 213), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 213; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/No-percolation-at-criticality-on-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Criticality/MainSparseBoundary.lean (declaration OAI.CriticalPercolation.BondGraph.main_failure_sparse_polynomial)

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

theorem main_failure_sparse_polynomial [Infinite V]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (hpc : G.criticalProbability<1)
    (hper : G.law G.criticalProbability G.percolates≠0) :
    G.SubexponentialGrowth ∧ G.CombinatoriallyUnimodular ∧
      ∃ d : ℕ, 2≤d ∧ ∀ R : ℕ, ∃ n≥R, ∃ v : V, (G.vertexBall v n).ncard≤n^d := by
  sorry

end CriticalPercolation.BondGraph
end
end

end OAI
end
