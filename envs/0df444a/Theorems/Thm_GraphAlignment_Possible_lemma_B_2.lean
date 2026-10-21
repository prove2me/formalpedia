-- Prove2me | Theorems.Thm_GraphAlignment_Possible_lemma_B_2
-- name    : GraphAlignment.Possible.lemma_B_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T02:31:01.888988+00:00
-- url     : https://prove2.me/theorems/77b1e84b-dcc9-49c2-af78-6729eb205013
-- title:
--   Lemma B.2, p. 23 — the moment generating function of a cyclic sum W = A₀B₁ + … + AₙB₀ of correlated edge pairs
-- statement:
--   Let $0 \le q < s \le 1$ and let $(A_0,B_0), \dots, (A_n,B_n)$ be $n+1$ independent pairs of $\{0,1\}$-valued random variables, each with the law $P$ of (3): $p_{00} = 1-2q+qs$, $p_{01} = p_{10} = q(1-s)$, $p_{11} = qs$. Assume the covariance $\sigma^2 = q(s-q)$ of $A_i$ and $B_i$ is positive. Define the cyclic sum
--   $$W = A_0B_1 + A_1B_2 + \dots + A_{n-1}B_n + A_nB_0 .$$
--   Then for every $t > 0$,
--   $$\mathbb E\big[e^{tW}\big] = \Big(\frac{T + \sqrt{T^2 - 4D}}{2}\Big)^{n+1} + \Big(\frac{T - \sqrt{T^2 - 4D}}{2}\Big)^{n+1},$$
--   where $T = p_{11}(e^t - 1) + 1$ and $D = \sigma^2(e^t - 1)$.
--
--   This is the moment generating function of the contribution of one cycle of the permutation $p$ to $\sum A_{ij}B'_{p(i)p(j)}$, the key computation in the union bound of Proposition 4.4.
--
--   **Formalization Note** The expectation is the finite sum over all $(n+1)$-tuples of edge states in `Bool × Bool`, weighted by $\prod_i P(\omega_i)$; indices are in `Fin (n+1)` with cyclic addition, so the last term is $A_nB_0$ (for $n = 0$, $W = A_0B_0$). $\sigma^2 = q(s-q)$ is (2), and $\sigma^2 > 0$ is the lemma's hypothesis. $T^2 - 4D \ge 0$ holds under these assumptions, so the square root is the real one.
-- source:
--   Hall, Massoulié, Partial Recovery in the Graph Alignment Problem, arXiv:2007.00533v5, p. 23, Lemma B.2; p. 7, (2)–(3)

import Mathlib
import Definitions.Def_GraphAlignment_Possible_Setting

namespace GraphAlignment.Possible

theorem lemma_B_2 (n : ℕ) (q s t : ℝ) (hq : 0 ≤ q) (hqs : q < s) (hs : s ≤ 1)
    (hσ : 0 < q * (s - q)) (ht : 0 < t) :
    let T : ℝ := q * s * (Real.exp t - 1) + 1
    let D : ℝ := q * (s - q) * (Real.exp t - 1)
    let W : (Fin (n + 1) → Bool × Bool) → ℝ := fun ω =>
      ∑ i : Fin (n + 1), (if (ω i).1 && (ω (i + 1)).2 then (1 : ℝ) else 0)
    ∑ ω : Fin (n + 1) → Bool × Bool, (∏ i, pLaw q s (ω i)) * Real.exp (t * W ω) =
      ((T + Real.sqrt (T ^ 2 - 4 * D)) / 2) ^ (n + 1) +
        ((T - Real.sqrt (T ^ 2 - 4 * D)) / 2) ^ (n + 1) := by sorry

end GraphAlignment.Possible
