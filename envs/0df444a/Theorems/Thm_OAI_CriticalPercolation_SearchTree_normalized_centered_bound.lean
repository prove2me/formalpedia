-- Prove2me | Theorems.Thm_OAI_CriticalPercolation_SearchTree_normalized_centered_bound
-- name    : OAI.CriticalPercolation.SearchTree.normalized_centered_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T17:26:14.195699+00:00
-- url     : https://prove2.me/theorems/3bcbe974-7fcf-4908-88b5-e477c9f10ef3
-- title:
--   OAI.CriticalPercolation.SearchTree.normalized_centered_bound: intermediate lemma from OpenAI, No percolation at criticality on quasi-transitive graphs (result family 213)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CriticalPercolation.BondGraph.no_percolation_at_criticality`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *No percolation at criticality on quasi-transitive graphs (result family 213)*, OpenAI Math Release, September 24, 2026, result family 213, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CriticalPercolation.SearchTree.normalized_centered_bound` of [lean/OAI/Probability/CriticalPercolation/Exploration/QueryNormalized.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Exploration/QueryNormalized.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CriticalPercolation.SearchTree`, with `open scoped Classical`, `open FiniteProduct`):
--
--   ```lean
--   lemma normalized_centered_bound (t : SearchTree E R) (used : Finset E) (ht : t.Valid used)
--       (p : ℝ) (hp : p ∈ Set.Icc 0 1) (w : E → Prop → ℝ)
--       (hw : ∀ e, ∑ b, w e b = 1) (hn : ∀ e b, 0≤w e b)
--       (hf : LazyDFS.Fresh w p used) (K : ℕ) :
--       expect w (fun ω => |t.centeredSum p ω| *
--         min (1/(4:ℝ)^K) (1/(t.queryCount ω : ℝ))) ≤ 6/(2:ℝ)^K
--   ```
--
--   **Definitions.** The statement is written with `OAI.CriticalPercolation.SearchTree` and `OAI.CriticalPercolation.FiniteProduct.expect` (definitions bundle `OAIQ228B000` of this split); `OAI.CriticalPercolation.LazyDFS.Fresh` (definitions bundle `OAIQ228B001` of this split); `OAI.CriticalPercolation.SearchTree.Valid`, `OAI.CriticalPercolation.SearchTree.centeredSum` and `OAI.CriticalPercolation.SearchTree.queryCount` (definitions bundle `OAIQ228B002` of this split).
--
--   **Used by.** The proofs of `OAI.CriticalPercolation.BondGraph.UnimodularRoot.critical_atMostOneInfinite_ae` and `OAI.CriticalPercolation.BondGraph.subexponential_adjacent_bound` of this split import it.
-- source:
--   OpenAI, No percolation at criticality on quasi-transitive graphs (result family 213), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 213; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/No-percolation-at-criticality-on-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Exploration/QueryNormalized.lean (declaration OAI.CriticalPercolation.SearchTree.normalized_centered_bound)

import Mathlib
import Definitions.Def_OAIQ228B002

section

attribute [-instance] _root_.OAI.CriticalPercolation.Priority.instFintypeOrder _root_.OAI.CriticalPercolation.QueryTree.leafFintype _root_.OAI.CriticalPercolation.QueryTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace CriticalPercolation.SearchTree
open scoped Classical
open FiniteProduct

variable {E R : Type*} [Fintype E] [DecidableEq E]

lemma normalized_centered_bound (t : SearchTree E R) (used : Finset E) (ht : t.Valid used)
    (p : ℝ) (hp : p ∈ Set.Icc 0 1) (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (hn : ∀ e b, 0≤w e b)
    (hf : LazyDFS.Fresh w p used) (K : ℕ) :
    expect w (fun ω => |t.centeredSum p ω| *
      min (1/(4:ℝ)^K) (1/(t.queryCount ω : ℝ))) ≤ 6/(2:ℝ)^K := by
  sorry

end CriticalPercolation.SearchTree
end
end
end

end OAI
end
