-- Prove2me | Theorems.Thm_OAI_AlgorithmicThinTrees_GraphicHalf_sparsification_correct_explicit
-- name    : OAI.AlgorithmicThinTrees.GraphicHalf.sparsification_correct_explicit
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T12:06:35.469202+00:00
-- url     : https://prove2.me/theorems/4218b0da-2194-4031-8017-07c8f6089e60
-- title:
--   One sparsification round is correct for every r ≥ 2^2048 (explicit-cutoff form of OpenAI's lemma)
-- statement:
--   This is OpenAI's lemma `OAI.AlgorithmicThinTrees.GraphicHalf.sparsification_correct` (intermediate lemma of OpenAI, *A polynomial-time construction of strong thin trees (result family 174)*, OpenAI Math Release, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), restated with an explicit cutoff. Same namespace, same `open`s, same bundles, and the same conclusion word for word. The only change is the quantifier prefix: the published lemma begins "there is $R \ge 4$ such that for every $r \ge R$". This one begins "for every natural number $r \ge 2^{2048}$". In OpenAI's terms, it says that `RoundBound (2^2048)` holds.
--
--   So, for every $r \ge 2^{2048}$ and every multigraph $G$ on $d+1 \ge 2$ vertices that packs $r$ edge-disjoint spanning trees, the next count $r'$ = `nextCount r` and the edge set $A$ = `sparsify G r` satisfy all of the following:
--   - $r/4 \le r' \le r/2$ and $r' > 0$;
--   - $A$ packs $r'$ spanning trees;
--   - every cut of $G$ meets $A$ in at most $(1/2 + 3h_r)$ times its size;
--   - $(1/2 + 3h_r)\,r \le (1 + 80u_r)\,r'$.
--
--   Here $h_r$ is `halfError r` and $u_r = r^{-1/16}$ is `errorU r`.
--
--   Why it exists: OpenAI's tree algorithm with round threshold $R$ produces trees of thinness $3R\,e^{B}$, with $B$ = `lossB`, and OpenAI proves only that a valid $R$ exists. With $R = 2^{2048}$ the thinness constant is explicit. The proof is OpenAI's, using `shortcut_correct_explicit` and an explicit check of OpenAI's `Numeric r`.
-- source:
--   OpenAI, A polynomial-time construction of strong thin trees (result family 174), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (Apache License 2.0), explicit-cutoff form (r ≥ 2^2048) of OAI.AlgorithmicThinTrees.GraphicHalf.sparsification_correct

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

namespace AlgorithmicThinTrees.GraphicHalf
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph
open MetricTests MetricTests.RationalStep Normalization RationalSigning
open scoped MatrixOrder
variable {d m : ℕ}

theorem sparsification_correct_explicit : ∀r : ℕ, 2^2048 ≤ r →
    ∀(d m : ℕ) (G : MultiGraph (d+1) m), 2 ≤ d+1 → G.TreePackable univ r →
      (r:ℝ)/4 ≤ nextCount r ∧ (nextCount r:ℝ) ≤ (r:ℝ)/2 ∧ 0 < nextCount r ∧
      G.TreePackable (sparsify G r) (nextCount r) ∧
      (∀S : Finset (Fin (d+1)), ((G.cut (sparsify G r) S).card:ℝ) ≤
        (1/2+3*halfError r)*(G.cut univ S).card) ∧
      (1/2+3*halfError r)*(r:ℝ) ≤ (1+80*errorU r)*nextCount r := by
  sorry

end AlgorithmicThinTrees.GraphicHalf
end

end OAI
end
