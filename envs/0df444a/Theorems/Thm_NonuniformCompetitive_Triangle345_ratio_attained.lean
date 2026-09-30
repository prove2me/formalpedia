-- Prove2me | Theorems.Thm_NonuniformCompetitive_Triangle345_ratio_attained
-- name    : NonuniformCompetitive.Triangle345.ratio_attained
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T11:11:45.45067+00:00
-- url     : https://prove2.me/theorems/2aee51e3-6d31-47f6-a1df-70f50c1cfa9e
-- title:
--   Theorem 13 (second claim) — a randomized two-server algorithm on the 3-4-5 triangle is $1652/1069$-competitive
-- statement:
--   Let $M$ be a metric space with exactly three points $a,b,c$, where $d(a,b)=3$, $d(a,c)=5$ and $d(b,c)=4$, and fix an initial configuration $C_0$ of two labelled servers on $M$. For the two-server problem on $M$ (each request must be covered by a server once it is issued; the cost is the total distance moved), a randomized on-line algorithm is a probability distribution over deterministic on-line algorithms starting in $C_0$, with measurable cost on each request sequence.
--
--   The claim is that some randomized on-line algorithm $A$ starting in $C_0$ is $1652/1069$-competitive against an oblivious adversary: there is a constant $a$ such that for every request sequence $\sigma$,
--   $$\mathbf{E}C_A(\sigma) \le \frac{1652}{1069}\cdot C_{opt}(\sigma) + a,$$
--   where $C_{opt}(\sigma)$ is the optimal off-line cost of serving $\sigma$ from $C_0$.
--
--   This is the upper-bound half of Theorem 13; together with the lower bound it shows $1652/1069$ is the exact optimal randomized competitive factor on this triangle.
--
--   **Formalization Note** The model is the platform's `KServer_model` / `KServer_randomized`; the additive constant $a$ is any real number and may depend on $C_0$. The claim is stated for every initial configuration, including both servers on the same point.
-- source:
--   Karlin, Manasse, McGeoch, Owicki, Competitive Randomized Algorithms for Nonuniform Problems, Algorithmica 11 (1994), pp. 566–567, Theorem 13, second claim (attainment); competitiveness defined on p. 543

import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_KServer_randomized

namespace NonuniformCompetitive.Triangle345

/-- Karlin–Manasse–McGeoch–Owicki (Algorithmica 11, 1994), Theorem 13, second claim (p. 567):
for the two-server problem on the three-point metric space `{a, b, c}` with `d(a,b) = 3`,
`d(a,c) = 5`, `d(b,c) = 4`, and every initial configuration `C₀`, some randomized on-line
algorithm starting from `C₀` is `1652/1069`-competitive against an oblivious adversary. -/
theorem ratio_attained
    {M : Type} [MetricSpace M] (a b c : M) (hM : ∀ x : M, x = a ∨ x = b ∨ x = c)
    (hab : dist a b = 3) (hac : dist a c = 5) (hbc : dist b c = 4)
    (C₀ : KServer.Config 2 M) :
    ∃ A : KServer.RandomizedAlgorithm 2 M, A.IsCompetitiveFrom C₀ (1652 / 1069) := by sorry

end NonuniformCompetitive.Triangle345
