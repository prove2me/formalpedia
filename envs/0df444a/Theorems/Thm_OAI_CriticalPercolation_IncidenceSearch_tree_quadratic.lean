-- Prove2me | Theorems.Thm_OAI_CriticalPercolation_IncidenceSearch_tree_quadratic
-- name    : OAI.CriticalPercolation.IncidenceSearch.tree_quadratic
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T17:24:22.986206+00:00
-- url     : https://prove2.me/theorems/3379c8ba-641b-476b-bd84-a506555cf7d9
-- title:
--   OAI.CriticalPercolation.IncidenceSearch.tree_quadratic: intermediate lemma from OpenAI, No percolation at criticality on quasi-transitive graphs (result family 213)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CriticalPercolation.BondGraph.no_percolation_at_criticality`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *No percolation at criticality on quasi-transitive graphs (result family 213)*, OpenAI Math Release, September 24, 2026, result family 213, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CriticalPercolation.IncidenceSearch.tree_quadratic` of [lean/OAI/Probability/CriticalPercolation/Modular/WeightedIncidenceSearch.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Modular/WeightedIncidenceSearch.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CriticalPercolation.IncidenceSearch`, with `open Set`, `open scoped Classical`):
--
--   ```lean
--   lemma tree_quadratic (G : BondGraph V E) (v : V) (ω : Set E) (a : E → ℝ) :
--       (tree G v).quadraticCost a ω = ∑ e,
--         if e∈G.incidentEdges (G.cluster ω v) then (a e)^2 else 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.CriticalPercolation.BondGraph.incidentEdges` (definitions bundle `OAIQ228B000` of this split); `OAI.CriticalPercolation.IncidenceSearch.State` (definitions bundle `OAIQ228B001` of this split); `OAI.CriticalPercolation.IncidenceSearch.tree` and `OAI.CriticalPercolation.SearchTree.quadraticCost` (definitions bundle `OAIQ228B002` of this split); `OAI.CriticalPercolation.BondGraph` and `OAI.CriticalPercolation.BondGraph.cluster` (the published bundle `Def_CriticalPercolation`).
--
--   **Used by.** The proof of `OAI.CriticalPercolation.BondGraph.restriction_weighted_quadratic_le` of this split imports it.
-- source:
--   OpenAI, No percolation at criticality on quasi-transitive graphs (result family 213), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 213; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/No-percolation-at-criticality-on-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Modular/WeightedIncidenceSearch.lean (declaration OAI.CriticalPercolation.IncidenceSearch.tree_quadratic)

import Mathlib
import Definitions.Def_CriticalPercolation
import Definitions.Def_OAIQ228B002

section

attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation.IncidenceSearch
variable {V E : Type*}

variable [Fintype E]

lemma tree_quadratic (G : BondGraph V E) (v : V) (ω : Set E) (a : E → ℝ) :
    (tree G v).quadraticCost a ω = ∑ e,
      if e∈G.incidentEdges (G.cluster ω v) then (a e)^2 else 0 := by
  sorry

end CriticalPercolation.IncidenceSearch
end
end

end OAI
end
