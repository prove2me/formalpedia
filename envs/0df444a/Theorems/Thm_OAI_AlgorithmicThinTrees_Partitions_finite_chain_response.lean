-- Prove2me | Theorems.Thm_OAI_AlgorithmicThinTrees_Partitions_finite_chain_response
-- name    : OAI.AlgorithmicThinTrees.Partitions.finite_chain_response
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T22:54:41.131951+00:00
-- url     : https://prove2.me/theorems/7bf24091-ce69-4e6f-82d4-ca71cfa40b5c
-- title:
--   OAI.AlgorithmicThinTrees.Partitions.finite_chain_response: intermediate lemma from OpenAI, A polynomial-time construction of strong thin trees (result family 174)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AlgorithmicThinTrees.algorithmic_strong_thin_trees`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A polynomial-time construction of strong thin trees (result family 174)*, OpenAI Math Release, September 23, 2026, result family 174, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AlgorithmicThinTrees.Partitions.finite_chain_response` of [lean/OAI/Combinatorics/ThinTrees/Continuation/PartitionResponse.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/ThinTrees/Continuation/PartitionResponse.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AlgorithmicThinTrees.Partitions`, with `open Finset Matrix StrongThinTree StrongThinTree.MultiGraph`, `open scoped Classical MatrixOrder`, `open MetricTests`):
--
--   ```lean
--   theorem finite_chain_response :
--       ∃r0 : ℕ, 2 ≤ r0 ∧ ∀r : ℕ, r0 ≤ r →
--         ∀(n m : ℕ) (H : MultiGraph n m), 2 ≤ n → H.Connected univ →
--         ∀(F : Finset (Fin m)) (J : Finset (Setoid (Fin n))),
--         IsChain (· ≤ ·) (J : Set (Setoid (Fin n))) →
--         (∀p ∈ J, ∀A ∈ parts p, (H.restrict F).EdgeConnectedReal A (r/2:ℕ)) →
--         (H.restrict F).EdgeConnectedReal univ (r/2:ℕ) →
--         ∀s : ℝ, 0 < s → s ≤ (r:ℝ)^(1/4:ℝ) →
--         ∃Y ∈ metricDomain H, CenteredPositive Y ∧ ∀p ∈ J,
--           (((crossing H p ∩ F).filter (fun e =>
--             ¬ (6*s) • vecMulVec (H.incidence e) (H.incidence e) ≤ Y)).card:ℝ) ≤
--             (r:ℝ)^(-1/3:ℝ)*(crossing H p ∩ F).card
--   ```
--
--   **Definitions.** The statement is written with `OAI.AlgorithmicThinTrees.Partitions.crossing` (definitions bundle `OAIQ241TT000` of this split); `OAI.StrongThinTree.MultiGraph.incidence` (definitions bundle `OAIQ241TT001` of this split); `OAI.AlgorithmicThinTrees.Partitions.parts`, `OAI.StrongThinTree.MultiGraph.EdgeConnectedReal` and `OAI.StrongThinTree.MultiGraph.restrict` (definitions bundle `OAIQ241TT002` of this split); `OAI.AlgorithmicThinTrees.MetricTests.CenteredPositive` and `OAI.AlgorithmicThinTrees.MetricTests.metricDomain` (definitions bundle `OAIQ241TT006` of this split); `OAI.StrongThinTree.MultiGraph` and `OAI.StrongThinTree.MultiGraph.Connected` (the published bundle `Def_AlgorithmicThinTrees`).
--
--   **Used by.** The proof of `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.uniform_search_response` of this split imports it.
-- source:
--   OpenAI, A polynomial-time construction of strong thin trees (result family 174), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 174; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-polynomial-time-construction-of-strong-thin-trees-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/ThinTrees/Continuation/PartitionResponse.lean (declaration OAI.AlgorithmicThinTrees.Partitions.finite_chain_response)

import Mathlib
import Definitions.Def_AlgorithmicThinTrees
import Definitions.Def_OAIQ241TT006

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace AlgorithmicThinTrees.Partitions
noncomputable section
open Finset Matrix StrongThinTree StrongThinTree.MultiGraph
open scoped Classical MatrixOrder

variable {n m : ℕ}

open MetricTests

theorem finite_chain_response :
    ∃r0 : ℕ, 2 ≤ r0 ∧ ∀r : ℕ, r0 ≤ r →
      ∀(n m : ℕ) (H : MultiGraph n m), 2 ≤ n → H.Connected univ →
      ∀(F : Finset (Fin m)) (J : Finset (Setoid (Fin n))),
      IsChain (· ≤ ·) (J : Set (Setoid (Fin n))) →
      (∀p ∈ J, ∀A ∈ parts p, (H.restrict F).EdgeConnectedReal A (r/2:ℕ)) →
      (H.restrict F).EdgeConnectedReal univ (r/2:ℕ) →
      ∀s : ℝ, 0 < s → s ≤ (r:ℝ)^(1/4:ℝ) →
      ∃Y ∈ metricDomain H, CenteredPositive Y ∧ ∀p ∈ J,
        (((crossing H p ∩ F).filter (fun e =>
          ¬ (6*s) • vecMulVec (H.incidence e) (H.incidence e) ≤ Y)).card:ℝ) ≤
          (r:ℝ)^(-1/3:ℝ)*(crossing H p ∩ F).card := by
  sorry

end
end AlgorithmicThinTrees.Partitions
end

end OAI
end
