-- Prove2me | Theorems.Thm_NonmonotoneSubmod_LocalSearch_ls_run_value_growth
-- name    : NonmonotoneSubmod.LocalSearch.ls_run_value_growth
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T21:06:13.783498+00:00
-- url     : https://prove2.me/theorems/303102e8-0ca0-4a64-87e9-9a142e0fab2c
-- title:
--   §3.1, proof of Theorem 3.4, last paragraph — $f(S_k) \ge (1+\epsilon/n^2)^k f(\{v\})$
-- statement:
--   Let $f : 2^X \to \mathbb{R}$ be a set function on a finite ground set $X$ with $n = |X|$, and let $\epsilon > 0$. For every run $S_0 = \{v\}, S_1, \dots, S_k$ of $k$ steps of Algorithm LS (started at a singleton of maximum value),
--
--   $$f(S_k) \ge \Big(1 + \frac{\epsilon}{n^2}\Big)^k f(\{v\}).$$
--
--   Each iteration of the algorithm, an addition or a removal, multiplies the value by more than $1 + \epsilon/n^2$; this is the growth half of the running-time bound.
--
--   **Formalization Note** The positivity $\epsilon > 0$ is implicit in the paper (the acceptance factor must exceed $1$) and is stated. No sign condition on $f$ is needed.
-- source:
--   Feige, Mirrokni, Vondrák, Maximizing Non-Monotone Submodular Functions, SIAM J. Comput. 40(4), 2011, p. 1141, §3.1, proof of Theorem 3.4, last paragraph ("if we iterate k times, then f(S) ≥ (1 + ϵ/n²)^k f({v})")

import Mathlib
import Definitions.Def_NonmonotoneSubmod_LocalSearch_LSAlgorithm

namespace NonmonotoneSubmod.LocalSearch

/-- Feige–Mirrokni–Vondrák 2011, §3.1, proof of Theorem 3.4, p. 1141, last paragraph: each
iteration of Algorithm LS increases the value by a factor of at least `1 + ε/n²`, so after `k`
steps from the start `{v}`, `f(S_k) ≥ (1 + ε/n²)^k f({v})`. -/
theorem ls_run_value_growth {X : Type} [Fintype X] [DecidableEq X] (ε : ℝ) (hε : 0 < ε)
    (f : Finset X → ℝ) (S : ℕ → Finset X) (k : ℕ) (hrun : IsLSRun ε f S k) (v : X)
    (hv : S 0 = {v}) :
    (1 + ε / (Fintype.card X : ℝ) ^ 2) ^ k * f {v} ≤ f (S k) := by sorry

end NonmonotoneSubmod.LocalSearch
