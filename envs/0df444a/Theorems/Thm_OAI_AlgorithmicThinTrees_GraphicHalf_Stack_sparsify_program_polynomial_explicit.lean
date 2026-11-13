-- Prove2me | Theorems.Thm_OAI_AlgorithmicThinTrees_GraphicHalf_Stack_sparsify_program_polynomial_explicit
-- name    : OAI.AlgorithmicThinTrees.GraphicHalf.Stack.sparsify_program_polynomial_explicit
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T12:06:52.228233+00:00
-- url     : https://prove2.me/theorems/c9af5966-7baa-40ac-a8b4-b9060ab25403
-- title:
--   The sparsification program runs in polynomial time once r ≥ 2^2048 (explicit-cutoff form of OpenAI's lemma)
-- statement:
--   This is OpenAI's lemma `OAI.AlgorithmicThinTrees.GraphicHalf.Stack.sparsify_program_polynomial` (intermediate lemma of OpenAI, *A polynomial-time construction of strong thin trees (result family 174)*, OpenAI Math Release, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), restated with an explicit cutoff. Same namespace, same `open`s, same bundles, and the same conclusion word for word. The published lemma begins "there is $R \ge 4$ such that, for every family of problems with $R \le r$ …". This one fixes $R = 2^{2048}$.
--
--   So, for every index type $\iota$, every size function $L$ and every family $a$ of OpenAI `Problem`s such that:
--   - the encoded problems are polynomially bounded in $L$;
--   - every $a_i$ has $r \ge 2^{2048}$, at least two vertices and $r$ edge-disjoint spanning trees;
--
--   OpenAI's stack program `sparsifyProgram` runs on the family $a$ within a time polynomial in $L$ (`RunsPoly L sparsifyProgram a`).
--
--   Why it exists: OpenAI's tree algorithm needs a round threshold that both this lemma and `sparsification_correct_explicit` accept, and its thinness constant is proportional to that threshold. The proof is OpenAI's, using `shortcut_correct_explicit`.
-- source:
--   OpenAI, A polynomial-time construction of strong thin trees (result family 174), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (Apache License 2.0), explicit-cutoff form (R = 2^2048) of OAI.AlgorithmicThinTrees.GraphicHalf.Stack.sparsify_program_polynomial

import Mathlib
import Definitions.Def_OAIQ241TT014

section

attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace AlgorithmicThinTrees.GraphicHalf.Stack
open CurrentKS.Realization CurrentKS.CleanRoutine KS.W23 Matrix StrongThinTree Finset
open MetricTests MetricTests.RationalStep Normalization GraphStack
open MetricTests.RationalStep.Stack

theorem sparsify_program_polynomial_explicit : ∀{ι : Type} {L : ι → ℕ}
    (a : ι → Problem), IsPoly L (fun i => (problemCode (a i)).length) →
    (∀i, 2^2048 ≤ (a i).r ∧ 2 ≤ (a i).d+1 ∧ (a i).G.TreePackable univ (a i).r) →
    RunsPoly L sparsifyProgram a := by
  sorry

end AlgorithmicThinTrees.GraphicHalf.Stack
end

end OAI
end
