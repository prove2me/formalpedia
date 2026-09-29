-- Prove2me | Theorems.Thm_NonmonotoneSubmod_LocalSearch_ls_terminal_approx_local_optimum
-- name    : NonmonotoneSubmod.LocalSearch.ls_terminal_approx_local_optimum
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T21:03:30.553395+00:00
-- url     : https://prove2.me/theorems/1beb5a9a-35e2-44af-8da6-902b782d9586
-- title:
--   §3.1, p. 1141 — a terminal set of Algorithm LS is a $(1+\epsilon/n^2)$-approximate local optimum
-- statement:
--   Let $f : 2^X \to \mathbb{R}$ be a set function on a finite ground set $X$ with $n = |X|$, and let $\epsilon \in \mathbb{R}$. If Algorithm LS has terminated at $S$, that is, no addition step and no removal step of the algorithm applies to $S$, then $S$ is a $(1+\epsilon/n^2)$-approximate local optimum of $f$:
--
--   $$\Big(1 + \frac{\epsilon}{n^2}\Big) f(S) \ge f(S \setminus \{v\}) \ (v \in S), \qquad \Big(1 + \frac{\epsilon}{n^2}\Big) f(S) \ge f(S \cup \{v\}) \ (v \notin S).$$
--
--   This connects the algorithm to Definition 3.2, after which the analysis no longer refers to the algorithm.
--
--   **Formalization Note** Termination means that no step of the step relation (addition first, removal only when no addition applies) exists from $S$. No condition on $f$ or $\epsilon$ is needed.
-- source:
--   Feige, Mirrokni, Vondrák, Maximizing Non-Monotone Submodular Functions, SIAM J. Comput. 40(4), 2011, p. 1141, §3.1, sentence after Algorithm LS ("It is easy to see that if the algorithm terminates …")

import Mathlib
import Definitions.Def_NonmonotoneSubmod_LocalSearch_IsApproxLocalOptimum
import Definitions.Def_NonmonotoneSubmod_LocalSearch_LSAlgorithm

namespace NonmonotoneSubmod.LocalSearch

/-- Feige–Mirrokni–Vondrák 2011, §3.1, p. 1141, sentence after Algorithm LS: if Algorithm LS has
terminated at `S` (no step 2 addition and no step 3 removal applies), then `S` is a
`(1 + ε/n²)`-approximate local optimum of `f` (Definition 3.2), where `n = |X|`. -/
theorem ls_terminal_approx_local_optimum {X : Type} [Fintype X] [DecidableEq X] (ε : ℝ)
    (f : Finset X → ℝ) (S : Finset X) (hS : IsLSTerminal ε f S) :
    IsApproxLocalOptimum f (ε / (Fintype.card X : ℝ) ^ 2) S := by sorry

end NonmonotoneSubmod.LocalSearch
