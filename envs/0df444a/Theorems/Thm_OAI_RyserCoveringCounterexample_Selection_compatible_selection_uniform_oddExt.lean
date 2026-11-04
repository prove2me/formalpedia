-- Prove2me | Theorems.Thm_OAI_RyserCoveringCounterexample_Selection_compatible_selection_uniform_oddExt
-- name    : OAI.RyserCoveringCounterexample.Selection.compatible_selection_uniform_oddExt
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-03T23:19:48.558345+00:00
-- url     : https://prove2.me/theorems/0a56d9e5-0870-4e25-8455-8cf3e550d29c
-- title:
--   Compatible translates from independent pools
-- statement:
--   For every positive integer $D$ there is an integer $K\ge 6$ such that for every $\varepsilon>0$ there is a threshold $Q$ with the following property. Let $F$ be a finite field with $q=|F|\ge Q$ and let $n\le Dq$. For $1\le i\le n$ let $W_i\subseteq F^2$ and let $D_i$ be a set of directions with $|W_i|,|D_i|\le D$, and assume each direction belongs to $D_i$ for at most $D$ indices $i$. For distinct $i,j$, translates $b+W_i$ and $b'+W_j$ conflict if there are $u\in W_i$, $v\in W_j$ and $d\in D_i\cup D_j$ with
--
--   $$
--   (b+u)-(b'+v)\in d.
--   $$
--
--   Draw $K$ independent uniform shifts $b_{i,1},\dots,b_{i,K}\in F^2$ for each $i$, independently for all indices. Then with probability at least $1-\varepsilon$ there is a choice of indices $k_i\in\{1,\dots,K\}$ for which the translates $b_{i,k_i}+W_i$ have no conflicts.
--
--   This is Theorem 4.1 of the paper, proved through an independent-transversal argument in the tradition of Haxell. It separates the independent random choices needed by the deletion estimates from the geometric compatibility needed for exceptional edges to intersect.
-- source:
--   OpenAI, A counterexample to Ryser's covering conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Counterexample-to-Rysers-Covering-Conjecture-September-23-2026/paper.pdf; Apache License 2.0); Theorem 4.1. Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Ryser/Selection/Main.lean#L13 (declaration OAI.RyserCoveringCounterexample.Selection.compatible_selection_uniform; suffix _oddExt added for name uniqueness)

import Mathlib
import Definitions.Def_RyserOddSupport

namespace OAI

universe u

namespace RyserCoveringCounterexample.Selection

theorem compatible_selection_uniform_oddExt (D : ℕ) (hD : 1 ≤ D) :
    ∃ K : ℕ, 6 ≤ K ∧
      ∀ ε : ℝ, 0 < ε → ∃ Q : ℕ,
        ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F]
          (n : ℕ) (data : Data F n),
          Bounded D data → Q ≤ Fintype.card F →
            1 - ε ≤ (poolLaw F n K).prob
              (fun pool => HasCompatibleChoice data pool) := by
  sorry

end RyserCoveringCounterexample.Selection
end OAI
