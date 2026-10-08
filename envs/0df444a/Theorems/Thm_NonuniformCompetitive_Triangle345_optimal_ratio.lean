-- Prove2me | Theorems.Thm_NonuniformCompetitive_Triangle345_optimal_ratio
-- name    : NonuniformCompetitive.Triangle345.optimal_ratio
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T11:15:49.232307+00:00
-- url     : https://prove2.me/theorems/19c8cfdb-385d-4f40-9740-3604490c6d34
-- title:
--   Theorem 13 — the optimal randomized two-server ratio on the 3-4-5 triangle is $1652/1069$
-- statement:
--   Let $M$ be a metric space with exactly three points $a,b,c$, where $d(a,b)=3$, $d(a,c)=5$ and $d(b,c)=4$, and fix an initial configuration $C_0$ of two labelled servers on $M$. In the two-server problem on $M$, each request must be covered by a server once it is issued, and the cost is the total distance moved by the servers. A randomized on-line algorithm is a probability distribution over deterministic on-line algorithms starting in $C_0$, with measurable cost on each request sequence; it is $\rho$-competitive against an oblivious adversary if for some constant $a$ and every request sequence $\sigma$,
--   $$\mathbf{E}C_A(\sigma) \le \rho\cdot C_{opt}(\sigma) + a,$$
--   with $C_{opt}(\sigma)$ the optimal off-line cost of serving $\sigma$ from $C_0$.
--
--   The theorem (Theorem 13 of Karlin, Manasse, McGeoch and Owicki) asserts both:
--   1. no randomized algorithm is $\rho$-competitive for any $\rho < 1652/1069 \approx 1.545$;
--   2. some randomized algorithm is $1652/1069$-competitive.
--
--   Hence the optimal randomized competitive factor against an oblivious adversary on this triangle is exactly
--   $$\frac{1652}{1069}.$$
--   Since this exceeds $3/2 = H_2$, it shows that the harmonic-number bounds known for paging on uniform spaces do not extend to non-uniform metric spaces.
--
--   **Formalization Note** The model is the platform's `KServer_model` / `KServer_randomized`. The triangle is encoded by hypotheses on an arbitrary metric space. Both claims are stated for every initial configuration, including both servers on one point; the additive constant absorbs the start. The paper's "$\approx 1.545$" is a gloss; the constant is exactly $1652/1069$.
-- source:
--   Karlin, Manasse, McGeoch, Owicki, Competitive Randomized Algorithms for Nonuniform Problems, Algorithmica 11 (1994), pp. 566–567, Theorem 13; competitiveness defined on p. 543

import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_KServer_randomized

namespace NonuniformCompetitive.Triangle345

/-- Karlin–Manasse–McGeoch–Owicki (Algorithmica 11, 1994), Theorem 13 (pp. 566–567): on the
triangle with edge lengths 3, 4, 5 (`d(a,b) = 3`, `d(a,c) = 5`, `d(b,c) = 4`), the optimal
randomized competitive factor of the two-server problem against an oblivious adversary is exactly
`1652/1069`: no randomized algorithm starting from `C₀` is competitive within a smaller factor,
and some randomized algorithm starting from `C₀` achieves it. Stated for every initial
configuration `C₀`. -/
theorem optimal_ratio
    {M : Type} [MetricSpace M] (a b c : M) (hM : ∀ x : M, x = a ∨ x = b ∨ x = c)
    (hab : dist a b = 3) (hac : dist a c = 5) (hbc : dist b c = 4)
    (C₀ : KServer.Config 2 M) :
    (∀ (A : KServer.RandomizedAlgorithm 2 M) (ρ : ℝ), A.IsCompetitiveFrom C₀ ρ → (1652 / 1069 : ℝ) ≤ ρ) ∧
    ∃ A : KServer.RandomizedAlgorithm 2 M, A.IsCompetitiveFrom C₀ (1652 / 1069) := by sorry

end NonuniformCompetitive.Triangle345
