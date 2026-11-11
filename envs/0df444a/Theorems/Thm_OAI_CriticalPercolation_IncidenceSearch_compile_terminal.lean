-- Prove2me | Theorems.Thm_OAI_CriticalPercolation_IncidenceSearch_compile_terminal
-- name    : OAI.CriticalPercolation.IncidenceSearch.compile_terminal
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T17:23:55.142406+00:00
-- url     : https://prove2.me/theorems/66fd52b0-13b6-47ac-a304-53681b46f162
-- title:
--   OAI.CriticalPercolation.IncidenceSearch.compile_terminal: intermediate lemma from OpenAI, No percolation at criticality on quasi-transitive graphs (result family 213)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CriticalPercolation.BondGraph.no_percolation_at_criticality`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *No percolation at criticality on quasi-transitive graphs (result family 213)*, OpenAI Math Release, September 24, 2026, result family 213, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CriticalPercolation.IncidenceSearch.compile_terminal` of [lean/OAI/Probability/CriticalPercolation/Exploration/IncidenceSearch.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Exploration/IncidenceSearch.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CriticalPercolation.IncidenceSearch`, with `open Set`, `open scoped Classical`):
--
--   ```lean
--   lemma compile_terminal (G : BondGraph V E) (v : V) (ω : Set E) (n : ℕ) (st : State E)
--       (hs : Good G v ω st) (hn : Fintype.card E - st.read.card < n) :
--       let out := (compile G v n st).run (fun e => decide (e∈ω))
--       Good G v ω out ∧ ¬∃ e, Available G v out e
--   ```
--
--   **Definitions.** The statement is written with `OAI.CriticalPercolation.IncidenceSearch.State` (definitions bundle `OAIQ228B001` of this split); `OAI.CriticalPercolation.IncidenceSearch.Available`, `OAI.CriticalPercolation.IncidenceSearch.Good`, `OAI.CriticalPercolation.IncidenceSearch.compile` and `OAI.CriticalPercolation.SearchTree.run` (definitions bundle `OAIQ228B002` of this split); `OAI.CriticalPercolation.BondGraph` (the published bundle `Def_CriticalPercolation`).
--
--   **Used by.** The proofs of `OAI.CriticalPercolation.BondGraph.UnimodularRoot.critical_atMostOneInfinite_ae`, `OAI.CriticalPercolation.BondGraph.criticalProbability_pos`, `OAI.CriticalPercolation.BondGraph.expected_discrepancy_peakBand_fourth`, `OAI.CriticalPercolation.BondGraph.subexponential_adjacent_bound` and `OAI.CriticalPercolation.IncidenceSearch.tree_quadratic` of this split import it.
-- source:
--   OpenAI, No percolation at criticality on quasi-transitive graphs (result family 213), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 213; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/No-percolation-at-criticality-on-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Exploration/IncidenceSearch.lean (declaration OAI.CriticalPercolation.IncidenceSearch.compile_terminal)

import Mathlib
import Definitions.Def_CriticalPercolation
import Definitions.Def_OAIQ228B002

section

attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.OrderedQuery.localNodeDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation.IncidenceSearch

variable {V E : Type*} [DecidableEq E]

variable [Fintype E]

lemma compile_terminal (G : BondGraph V E) (v : V) (ω : Set E) (n : ℕ) (st : State E)
    (hs : Good G v ω st) (hn : Fintype.card E - st.read.card < n) :
    let out := (compile G v n st).run (fun e => decide (e∈ω))
    Good G v ω out ∧ ¬∃ e, Available G v out e := by
  sorry

end CriticalPercolation.IncidenceSearch
end
end
end

end OAI
end
