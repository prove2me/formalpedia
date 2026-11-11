-- Prove2me | Theorems.Thm_OAI_CriticalPercolation_SearchTree_restricted_weighted_event_fourth
-- name    : OAI.CriticalPercolation.SearchTree.restricted_weighted_event_fourth
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T17:25:11.160001+00:00
-- url     : https://prove2.me/theorems/e1a2e528-7956-4bde-a8ca-05ad2560f8e9
-- title:
--   OAI.CriticalPercolation.SearchTree.restricted_weighted_event_fourth: intermediate lemma from OpenAI, No percolation at criticality on quasi-transitive graphs (result family 213)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CriticalPercolation.BondGraph.no_percolation_at_criticality`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *No percolation at criticality on quasi-transitive graphs (result family 213)*, OpenAI Math Release, September 24, 2026, result family 213, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CriticalPercolation.SearchTree.restricted_weighted_event_fourth` of [lean/OAI/Probability/CriticalPercolation/Modular/WeightedQueryLaw.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Modular/WeightedQueryLaw.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CriticalPercolation.SearchTree`, with `open Set MeasureTheory`, `open scoped Classical ENNReal`):
--
--   ```lean
--   theorem restricted_weighted_event_fourth (s : Set E) [Fintype s] [DecidableEq s]
--       (a : s → ℝ) (t : SearchTree s R) (ht : t.Valid ∅) (p : unitInterval)
--       (B : ℝ) (hB : 0≤B) (h : Set E → ℝ≥0∞) (hm : Measurable h) (hh1 : ∀ ω, h ω≤1)
--       (hcost : ∀ ω, h ω≠0 → t.quadraticCost a (Subtype.val ⁻¹' ω)≤B) :
--       (∫⁻ ω : Set E, ENNReal.ofReal |t.weightedSum a p (Subtype.val ⁻¹' ω)| *h ω
--         ∂BernoulliProduct.law (fun _ => p))^4 ≤
--         ENNReal.ofReal (5*B^2)*(∫⁻ ω, h ω ∂BernoulliProduct.law (fun _ => p))^3
--   ```
--
--   **Definitions.** The statement is written with `OAI.CriticalPercolation.SearchTree` and `OAI.CriticalPercolation.BernoulliProduct.law` (definitions bundle `OAIQ228B000` of this split); `OAI.CriticalPercolation.SearchTree.Valid`, `OAI.CriticalPercolation.SearchTree.quadraticCost` and `OAI.CriticalPercolation.SearchTree.weightedSum` (definitions bundle `OAIQ228B002` of this split).
--
--   **Used by.** The proof of `OAI.CriticalPercolation.BondGraph.expected_discrepancy_peakBand_fourth` of this split imports it.
-- source:
--   OpenAI, No percolation at criticality on quasi-transitive graphs (result family 213), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 213; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/No-percolation-at-criticality-on-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Modular/WeightedQueryLaw.lean (declaration OAI.CriticalPercolation.SearchTree.restricted_weighted_event_fourth)

import Mathlib
import Definitions.Def_OAIQ228B002

section

attribute [-instance] _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace CriticalPercolation.SearchTree
variable {E R : Type*}

theorem restricted_weighted_event_fourth (s : Set E) [Fintype s] [DecidableEq s]
    (a : s → ℝ) (t : SearchTree s R) (ht : t.Valid ∅) (p : unitInterval)
    (B : ℝ) (hB : 0≤B) (h : Set E → ℝ≥0∞) (hm : Measurable h) (hh1 : ∀ ω, h ω≤1)
    (hcost : ∀ ω, h ω≠0 → t.quadraticCost a (Subtype.val ⁻¹' ω)≤B) :
    (∫⁻ ω : Set E, ENNReal.ofReal |t.weightedSum a p (Subtype.val ⁻¹' ω)| *h ω
      ∂BernoulliProduct.law (fun _ => p))^4 ≤
      ENNReal.ofReal (5*B^2)*(∫⁻ ω, h ω ∂BernoulliProduct.law (fun _ => p))^3 := by
  sorry

end CriticalPercolation.SearchTree
end
end

end OAI
end
