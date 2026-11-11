-- Prove2me | Theorems.Thm_OAI_AlgorithmicThinTrees_MetricTests_finite_continuation_inner_cube
-- name    : OAI.AlgorithmicThinTrees.MetricTests.finite_continuation_inner_cube
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T22:58:44.770984+00:00
-- url     : https://prove2.me/theorems/2f4431df-b09f-4632-b94a-63e6d27a142d
-- title:
--   OAI.AlgorithmicThinTrees.MetricTests.finite_continuation_inner_cube: intermediate lemma from OpenAI, A polynomial-time construction of strong thin trees (result family 174)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AlgorithmicThinTrees.algorithmic_strong_thin_trees`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A polynomial-time construction of strong thin trees (result family 174)*, OpenAI Math Release, September 23, 2026, result family 174, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AlgorithmicThinTrees.MetricTests.finite_continuation_inner_cube` of [lean/OAI/Combinatorics/ThinTrees/Continuation/FiniteContinuation.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/ThinTrees/Continuation/FiniteContinuation.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AlgorithmicThinTrees.MetricTests`, with `open Matrix Finset StrongThinTree StrongThinTree.MultiGraph Partitions Orientations`, `open scoped Classical MatrixOrder Matrix.Norms.Elementwise`):
--
--   ```lean
--   theorem finite_continuation_inner_cube (H : MultiGraph n m) (hn : 2 ≤ n)
--       (hconn : H.Connected univ) {s qbar β : ℝ}
--       (hs : 0 ≤ s) (hsP : s ≤ graphSize n m)
--       (hq : (graphSize n m)^(-12:ℤ) ≤ qbar) (hqm : qbar+β ≤ m)
--       (hβ : (graphSize n m)⁻¹/32 ≤ β)
--       (u : Fin m → ℝ) (hu : ∀e, 0 ≤ u e) {z : StepFree n m}
--       (hz : z ∈ stepFeasible H s (continuationBaseline m) (continuationStep m) (qbar+β+β) u) :
--       ∃(c : StepFree n m) (F : FlowPoint n m),
--         c.Bounded (6*graphSize n m) ∧ F.Bounded (6*graphSize n m) ∧
--         ∀(x : StepFree n m) (W : FlowPoint n m),
--           x.Close c ((graphSize n m)^(-50:ℤ)) →
--           W.Close F ((graphSize n m)^(-50:ℤ)) →
--           finiteStep H s (continuationBaseline m) (continuationStep m) qbar
--             ((graphSize n m)^(-10:ℤ)) u x W
--   ```
--
--   **Definitions.** The statement is written with `OAI.AlgorithmicThinTrees.MetricTests.StepFree`, `OAI.AlgorithmicThinTrees.MetricTests.continuationBaseline`, `OAI.AlgorithmicThinTrees.MetricTests.continuationStep`, `OAI.AlgorithmicThinTrees.MetricTests.graphSize` and `OAI.AlgorithmicThinTrees.Orientations.FlowPoint` (definitions bundle `OAIQ241TT001` of this split); `OAI.AlgorithmicThinTrees.MetricTests.StepFree.Bounded`, `OAI.AlgorithmicThinTrees.MetricTests.StepFree.Close`, `OAI.AlgorithmicThinTrees.Orientations.FlowPoint.Bounded` and `OAI.AlgorithmicThinTrees.Orientations.FlowPoint.Close` (definitions bundle `OAIQ241TT006` of this split); `OAI.AlgorithmicThinTrees.MetricTests.finiteStep` and `OAI.AlgorithmicThinTrees.MetricTests.stepFeasible` (definitions bundle `OAIQ241TT009` of this split); `OAI.StrongThinTree.MultiGraph` and `OAI.StrongThinTree.MultiGraph.Connected` (the published bundle `Def_AlgorithmicThinTrees`).
--
--   **Used by.** The proof of `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.uniform_search_response` of this split imports it.
-- source:
--   OpenAI, A polynomial-time construction of strong thin trees (result family 174), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 174; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-polynomial-time-construction-of-strong-thin-trees-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/ThinTrees/Continuation/FiniteContinuation.lean (declaration OAI.AlgorithmicThinTrees.MetricTests.finite_continuation_inner_cube)

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

namespace AlgorithmicThinTrees.MetricTests
noncomputable section
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph Partitions Orientations
open scoped Classical MatrixOrder Matrix.Norms.Elementwise
variable {n m : ℕ}

theorem finite_continuation_inner_cube (H : MultiGraph n m) (hn : 2 ≤ n)
    (hconn : H.Connected univ) {s qbar β : ℝ}
    (hs : 0 ≤ s) (hsP : s ≤ graphSize n m)
    (hq : (graphSize n m)^(-12:ℤ) ≤ qbar) (hqm : qbar+β ≤ m)
    (hβ : (graphSize n m)⁻¹/32 ≤ β)
    (u : Fin m → ℝ) (hu : ∀e, 0 ≤ u e) {z : StepFree n m}
    (hz : z ∈ stepFeasible H s (continuationBaseline m) (continuationStep m) (qbar+β+β) u) :
    ∃(c : StepFree n m) (F : FlowPoint n m),
      c.Bounded (6*graphSize n m) ∧ F.Bounded (6*graphSize n m) ∧
      ∀(x : StepFree n m) (W : FlowPoint n m),
        x.Close c ((graphSize n m)^(-50:ℤ)) →
        W.Close F ((graphSize n m)^(-50:ℤ)) →
        finiteStep H s (continuationBaseline m) (continuationStep m) qbar
          ((graphSize n m)^(-10:ℤ)) u x W := by
  sorry

end
end AlgorithmicThinTrees.MetricTests
end

end OAI
end
