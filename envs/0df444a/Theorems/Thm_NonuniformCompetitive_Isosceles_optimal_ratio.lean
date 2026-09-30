-- Prove2me | Theorems.Thm_NonuniformCompetitive_Isosceles_optimal_ratio
-- name    : NonuniformCompetitive.Isosceles.optimal_ratio
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T10:57:15.536268+00:00
-- url     : https://prove2.me/theorems/641c4ddf-0ccd-4376-807a-0496274431c1
-- title:
--   Theorem 12 — the optimal randomized two-server ratio on the 1-d-d isosceles triangle is $(e_{2d-1}+1/4d)/((e_{2d-1}-1)+1/2d)$
-- statement:
--   Let $d\ge 1$ be an integer and let $M$ be the **isosceles triangle** with edge lengths $1$, $d$, $d$: a metric space consisting of exactly three points $a$, $b$, $c$ with
--   $$\operatorname{dist}(a,b)=1,\qquad \operatorname{dist}(a,c)=\operatorname{dist}(b,c)=d.$$
--   In the **two-server problem** on $M$, two mobile servers occupy points of $M$; each request names a point, which must be covered by a server after the request is served, and the cost is the total distance the servers move. A **randomized on-line algorithm** is a probability distribution over deterministic on-line algorithms (each of which decides its configuration from the requests seen so far), and its expected cost on a request sequence $\sigma$ is $\mathbf{E}C_A(\sigma)$. Such an algorithm is **$\rho$-competitive against an oblivious adversary from the initial configuration $C_0$** if every algorithm in its support starts in $C_0$ and there is a constant $a$ such that, for every finite request sequence $\sigma$,
--   $$\mathbf{E}C_A(\sigma)\le \rho\cdot C_{opt}(\sigma)+a,$$
--   where $C_{opt}(\sigma)$ is the least cost of serving $\sigma$ from $C_0$ with full knowledge of $\sigma$.
--
--   Write $e_{2d-1}=\left(1+\frac{1}{2d-1}\right)^{2d-1}=\left(\frac{2d}{2d-1}\right)^{2d-1}$ and
--   $$\alpha_d=\frac{e_{2d-1}+1/4d}{(e_{2d-1}-1)+1/2d}.$$
--
--   **Theorem 12.** For every initial configuration $C_0$ of the two servers:
--   1. no randomized on-line algorithm is competitive against an oblivious adversary from $C_0$ within a factor less than
--   $$\frac{e_{2d-1}+1/4d}{(e_{2d-1}-1)+1/2d};$$
--   that is, if $A$ is $\rho$-competitive from $C_0$ then $\rho\ge\alpha_d$;
--   2. there is a randomized on-line algorithm that is $\alpha_d$-competitive against an oblivious adversary from $C_0$.
--
--   The ratio $\alpha_d$ equals $3/2$ on the equilateral triangle ($d=1$), increases with $d$, and tends to $e/(e-1)$. The deterministic optimal ratio on every such triangle is $2$, so randomization strictly helps.
--
--   **Formalization Note** The model is the platform's published `KServer_model` and `KServer_randomized` (labelled servers `Fin 2 → M`, a randomized algorithm as a probability measure over deterministic on-line algorithms whose cost on each sequence is measurable, expected cost as a lower Lebesgue integral in $[0,\infty]$, the off-line optimum as a real infimum over schedules starting at $C_0$). The triangle is any metric space whose points are exactly $a,b,c$ at the stated distances; every such space is isometric to the paper's triangle. The claim is stated for every initial configuration $C_0$, including both servers on one point; the paper's argument absorbs the initial partial phase into the additive constant.
-- source:
--   Karlin, Manasse, McGeoch, Owicki, Competitive Randomized Algorithms for Nonuniform Problems, Algorithmica 11 (1994), DOI 10.1007/BF01189993, p. 564, Theorem 12 (proof pp. 564–566)

import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_KServer_randomized
import Definitions.Def_NonuniformCompetitive_Isosceles_isoscelesRatio

namespace NonuniformCompetitive.Isosceles

/-- Theorem 12 (Karlin–Manasse–McGeoch–Owicki, Competitive Randomized Algorithms for Nonuniform
Problems, Algorithmica 11 (1994), p. 564). Consider the two-server problem on an isosceles
triangle with integer edge lengths `1, d, d` (`1 ≤ d`): a metric space consisting of exactly the
three points `a, b, c` with `dist a b = 1` and `dist a c = dist b c = d`. From every initial
configuration `C₀` of the two servers:
1. no randomized algorithm is competitive against an oblivious adversary within a factor less
   than `(e_{2d-1} + 1/(4d)) / ((e_{2d-1} - 1) + 1/(2d))`, and
2. some randomized algorithm achieves this competitive factor. -/
theorem optimal_ratio {M : Type} [MetricSpace M] (d : ℕ) (hd : 1 ≤ d) (a b c : M)
    (hM : ∀ x : M, x = a ∨ x = b ∨ x = c)
    (hab : dist a b = 1) (hac : dist a c = d) (hbc : dist b c = d)
    (C₀ : KServer.Config 2 M) :
    (∀ (A : KServer.RandomizedAlgorithm 2 M) (ρ : ℝ), A.IsCompetitiveFrom C₀ ρ →
        isoscelesRatio d ≤ ρ) ∧
      ∃ A : KServer.RandomizedAlgorithm 2 M, A.IsCompetitiveFrom C₀ (isoscelesRatio d) := by sorry

end NonuniformCompetitive.Isosceles
