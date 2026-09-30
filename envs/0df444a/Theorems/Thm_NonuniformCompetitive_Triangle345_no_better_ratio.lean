-- Prove2me | Theorems.Thm_NonuniformCompetitive_Triangle345_no_better_ratio
-- name    : NonuniformCompetitive.Triangle345.no_better_ratio
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T11:04:21.326071+00:00
-- url     : https://prove2.me/theorems/fa5d6e4e-f5bd-47a4-9c2d-c56090e30eed
-- title:
--   Theorem 13 (first claim) — no two-server algorithm on the 3-4-5 triangle beats $1652/1069$
-- statement:
--   Let $M$ be a metric space with exactly three points $a,b,c$, where $d(a,b)=3$, $d(a,c)=5$ and $d(b,c)=4$. Consider the two-server problem on $M$: a request sequence $\sigma$ is a finite list of points, each request must be covered by a server immediately after it is issued, and the cost is the total distance the servers move. Fix an initial configuration $C_0$ of the two (labelled) servers.
--
--   A randomized on-line algorithm $A$ is a probability distribution over deterministic on-line algorithms, all starting in $C_0$, whose cost on each fixed request sequence is a measurable function of the random choice; $\mathbf{E}C_A(\sigma)$ is its expected cost. $A$ is $\rho$-competitive against an oblivious adversary if there is a constant $a$ such that for every request sequence $\sigma$,
--   $$\mathbf{E}C_A(\sigma) \le \rho\cdot C_{opt}(\sigma) + a,$$
--   where $C_{opt}(\sigma)$ is the optimal off-line cost of serving $\sigma$ from $C_0$.
--
--   The claim is that no randomized algorithm is competitive within a factor below $1652/1069\approx1.545$: if $A$ is $\rho$-competitive, then
--   $$\rho \ge \frac{1652}{1069}.$$
--
--   This is the lower-bound half of Theorem 13. It shows that the harmonic-number bound $H_2 = 3/2$ achievable on uniform metric spaces cannot be achieved on this non-uniform triangle.
--
--   **Formalization Note** The model is the platform's `KServer_model` / `KServer_randomized`. Deterministic algorithms are the point-mass case of randomized ones, so the statement covers them. The triangle is encoded by hypotheses on an arbitrary metric space ($M$ is covered by $a,b,c$, plus the three distances). The claim is stated for every initial configuration, including both servers on the same point.
-- source:
--   Karlin, Manasse, McGeoch, Owicki, Competitive Randomized Algorithms for Nonuniform Problems, Algorithmica 11 (1994), pp. 566–567, Theorem 13, first claim (lower bound); competitiveness defined on p. 543

import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_KServer_randomized

namespace NonuniformCompetitive.Triangle345

/-- Karlin–Manasse–McGeoch–Owicki (Algorithmica 11, 1994), Theorem 13, first claim (p. 567):
for the two-server problem on the three-point metric space `{a, b, c}` with `d(a,b) = 3`,
`d(a,c) = 5`, `d(b,c) = 4`, no randomized on-line algorithm (a mixed strategy over deterministic
on-line algorithms, which include the deterministic ones as point masses) starting from the
configuration `C₀` is `ρ`-competitive against an oblivious adversary for any `ρ < 1652/1069`.
Stated for every initial configuration `C₀`, including both servers on one point. -/
theorem no_better_ratio
    {M : Type} [MetricSpace M] (a b c : M) (hM : ∀ x : M, x = a ∨ x = b ∨ x = c)
    (hab : dist a b = 3) (hac : dist a c = 5) (hbc : dist b c = 4)
    (C₀ : KServer.Config 2 M) :
    (∀ (A : KServer.RandomizedAlgorithm 2 M) (ρ : ℝ), A.IsCompetitiveFrom C₀ ρ → (1652 / 1069 : ℝ) ≤ ρ) := by sorry

end NonuniformCompetitive.Triangle345
