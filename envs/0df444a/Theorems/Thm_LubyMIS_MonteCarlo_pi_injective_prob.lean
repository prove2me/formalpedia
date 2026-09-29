-- Prove2me | Theorems.Thm_LubyMIS_MonteCarlo_pi_injective_prob
-- name    : LubyMIS.MonteCarlo.pi_injective_prob
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T22:50:12.697866+00:00
-- url     : https://prove2.me/theorems/1552a451-d1ab-42ae-988b-c0bd0c0f1413
-- title:
--   §3.2 — π is a random reordering with probability at least 1 − 1/2n²
-- statement:
--   Let $n \ge 1$ be the number of vertices of the input graph, and let $V'$ be a vertex set with $|V'| \le n$. In Algorithm A every vertex $i \in V'$ draws a priority $\pi(i)$ uniformly from $\{1, \dots, n^4\}$, independently of the others. Then the priorities are pairwise distinct with probability at least $1 - 1/(2n^2)$:
--   $$\Pr_A\big[\pi \text{ is injective on } V'\big] \;\ge\; 1 - \frac{1}{2n^2}.$$
--
--   When the priorities are distinct they induce a total order on $V'$, and by symmetry this order is a uniformly random permutation; this is what the paper means by "$\pi$ is a random reordering of the vertices". The bound lets the analysis of Algorithm A (Lemma A) work with a uniform random permutation at the cost of the factor $1 - 1/(2n^2)$.
--
--   **Formalization Note** The formal statement asserts only the probability bound for injectivity; the fact that, conditioned on injectivity, the induced order is uniform is a symmetry fact that the statement does not include.
-- source:
--   Luby, A Simple Parallel Algorithm for the Maximal Independent Set Problem, SIAM J. Comput. 15(4), 1986, p. 1040, §3.2, first paragraph ("π is a random reordering of the vertices with probability at least 1 − 1/2n²")

import Mathlib
import Definitions.Def_LubyMIS_MonteCarlo_Basic

namespace LubyMIS.MonteCarlo

/-- Luby 1986, §3.2, p. 1040: under Algorithm A's law (priorities mutually independent and uniform on
`{1, …, n⁴}`), the priorities are pairwise distinct with probability at least `1 − 1/(2n²)`, where
`n ≥ max(1, |V′|)` is the number of vertices of the input graph. -/
theorem pi_injective_prob {V : Type*} [Fintype V] [DecidableEq V] (n : ℕ) (hn : 1 ≤ n)
    (hV : Fintype.card V ≤ n) :
    probA (V := V) n (fun π => Function.Injective π) ≥ 1 - 1 / (2 * (n : ℝ) ^ 2) := by sorry

end LubyMIS.MonteCarlo
