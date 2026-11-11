-- Prove2me | Theorems.Thm_OAI_AlgorithmicThinTrees_MetricTests_RationalStep_uniform_search_response
-- name    : OAI.AlgorithmicThinTrees.MetricTests.RationalStep.uniform_search_response
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T22:57:17.30881+00:00
-- url     : https://prove2.me/theorems/c8cd4762-6688-4539-88cb-5e1eb6e18e72
-- title:
--   OAI.AlgorithmicThinTrees.MetricTests.RationalStep.uniform_search_response: intermediate lemma from OpenAI, A polynomial-time construction of strong thin trees (result family 174)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AlgorithmicThinTrees.algorithmic_strong_thin_trees`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A polynomial-time construction of strong thin trees (result family 174)*, OpenAI Math Release, September 23, 2026, result family 174, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.uniform_search_response` of [lean/OAI/Combinatorics/ThinTrees/Continuation/Iteration.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/ThinTrees/Continuation/Iteration.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AlgorithmicThinTrees.MetricTests.RationalStep`, with `open Matrix Finset StrongThinTree StrongThinTree.MultiGraph Partitions`, `open scoped MatrixOrder`):
--
--   ```lean
--   theorem uniform_search_response :
--       ∃r0 : ℕ, 8 ≤ r0 ∧ ∀r : ℕ, r0 ≤ r →
--         ∀(n m : ℕ) (H : MultiGraph n m), 2 ≤ n → H.Connected univ → r ≤ m →
--         ∀(u : Fin m → ℚ), (∀e, 0 ≤ (u e:ℝ)) → (∀e, (u e:ℝ) ≤ 1) →
--         ∀(s Q g : ℚ), 0 < (s:ℝ) → (s:ℝ) ≤ (r:ℝ)^(1/4:ℝ) →
--         3*(r:ℝ)/4 ≤ (Q:ℝ) → (Q:ℝ) ≤ r →
--         (r:ℝ)^(-1/8:ℝ) ≤ (g:ℝ) → (g:ℝ) ≤ 2*(r:ℝ)^(-1/8:ℝ) →
--         3 ≤ (g:ℝ)*r →
--         (∀p, 0 ≤ slack H.left H.right (fun e => (u e:ℝ)+continuationBaseline m) (Q:ℝ) p) →
--         (rational (search H s (target m r Q g) u)).real ∈
--           stepFeasible H (s:ℝ) (continuationBaseline m) (continuationStep m)
--             ((Q:ℝ)-2*(g:ℝ)*r*continuationStep m) (fun e => (u e:ℝ))
--   ```
--
--   **Definitions.** The statement is written with `OAI.AlgorithmicThinTrees.MetricTests.StepFree`, `OAI.AlgorithmicThinTrees.MetricTests.continuationBaseline`, `OAI.AlgorithmicThinTrees.MetricTests.continuationStep` and `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.target` (definitions bundle `OAIQ241TT001` of this split); `OAI.AlgorithmicThinTrees.Partitions.slack` (definitions bundle `OAIQ241TT002` of this split); `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.search` (definitions bundle `OAIQ241TT005` of this split); `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.rational` and `OAI.AlgorithmicThinTrees.MetricTests.StepRational.real` (definitions bundle `OAIQ241TT006` of this split); `OAI.AlgorithmicThinTrees.MetricTests.stepFeasible` (definitions bundle `OAIQ241TT009` of this split); `OAI.StrongThinTree.MultiGraph` and `OAI.StrongThinTree.MultiGraph.Connected` (the published bundle `Def_AlgorithmicThinTrees`).
--
--   **Used by.** The proof of `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.shortcut_correct` of this split imports it.
-- source:
--   OpenAI, A polynomial-time construction of strong thin trees (result family 174), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 174; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-polynomial-time-construction-of-strong-thin-trees-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/ThinTrees/Continuation/Iteration.lean (declaration OAI.AlgorithmicThinTrees.MetricTests.RationalStep.uniform_search_response)

import Mathlib
import Definitions.Def_AlgorithmicThinTrees
import Definitions.Def_OAIQ241TT009

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace AlgorithmicThinTrees.MetricTests.RationalStep
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph Partitions
open scoped MatrixOrder
variable {n m : ℕ}

theorem uniform_search_response :
    ∃r0 : ℕ, 8 ≤ r0 ∧ ∀r : ℕ, r0 ≤ r →
      ∀(n m : ℕ) (H : MultiGraph n m), 2 ≤ n → H.Connected univ → r ≤ m →
      ∀(u : Fin m → ℚ), (∀e, 0 ≤ (u e:ℝ)) → (∀e, (u e:ℝ) ≤ 1) →
      ∀(s Q g : ℚ), 0 < (s:ℝ) → (s:ℝ) ≤ (r:ℝ)^(1/4:ℝ) →
      3*(r:ℝ)/4 ≤ (Q:ℝ) → (Q:ℝ) ≤ r →
      (r:ℝ)^(-1/8:ℝ) ≤ (g:ℝ) → (g:ℝ) ≤ 2*(r:ℝ)^(-1/8:ℝ) →
      3 ≤ (g:ℝ)*r →
      (∀p, 0 ≤ slack H.left H.right (fun e => (u e:ℝ)+continuationBaseline m) (Q:ℝ) p) →
      (rational (search H s (target m r Q g) u)).real ∈
        stepFeasible H (s:ℝ) (continuationBaseline m) (continuationStep m)
          ((Q:ℝ)-2*(g:ℝ)*r*continuationStep m) (fun e => (u e:ℝ)) := by
  sorry

end AlgorithmicThinTrees.MetricTests.RationalStep
end

end OAI
end
