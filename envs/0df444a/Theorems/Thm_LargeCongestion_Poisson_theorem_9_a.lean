-- Prove2me | Theorems.Thm_LargeCongestion_Poisson_theorem_9_a
-- name    : LargeCongestion.Poisson.theorem_9_a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:26:30.155237+00:00
-- url     : https://prove2.me/theorems/ab4876d6-2ace-47d1-9591-20b104cc9c35
-- title:
--   Theorem 9(a), p. 39 — ρ_TV(L(S), Poisson(x)) ≤ (1 − e^{−x}) x^{−1} Σ p_i² ≤ p for a sum S of independent Bernoulli(p_i)
-- statement:
--   Let $n \ge 1$ and let $S = X_1 + \dots + X_n$ be a sum of independent Bernoulli variables with $\mathsf P(X_i = 1) = p_i \in (0,1)$. Put $x = \mathsf E[S] = p_1 + \dots + p_n$, $p = \max\{p_1,\dots,p_n\}$, and let $X \sim \mathrm{Poisson}(x)$. Then
--   $$\rho_{TV}(\mathcal L(S), \mathcal L(X)) \le (1 - e^{-x})\, x^{-1}\sum_{i=1}^n p_i^2 \le p .$$
--
--   This is the Barbour–Hall bound: a sum of many rare independent participations is close to Poisson, with an error controlled by the largest participation probability. It drives the total-variation conclusions of Proposition 1 and Theorem 2.
--
--   **Formalization Note** $\mathcal L(S)$ is the Poisson-binomial law built from the product weights; $n \ge 1$ makes $x > 0$, so $x^{-1}$ is a genuine inverse. $\rho_{TV}$ is `MarkovChainCLT.tvDist`.
-- source:
--   Cominetti, Scarsini, Schröder & Stier-Moses, Approximation and Convergence of Large Atomic Congestion Games, arXiv:2001.02797v7, p. 39, Appendix C, Theorem 9(a)

import Mathlib
import Definitions.Def_TotalVariationDist
import Definitions.Def_LargeCongestion_Poisson_PoissonCalculus

namespace LargeCongestion.Poisson

open MeasureTheory ProbabilityTheory

/-- Theorem 9(a), Appendix C, p. 39 (Barbour–Hall): for `S = X_1 + ⋯ + X_n` with independent
`X_i ∼ Bernoulli(p_i)`, `p_i ∈ (0, 1)`, `x = ∑ p_i`, `p = max p_i` and `X ∼ Poisson(x)`,
`ρ_TV(L(S), L(X)) ≤ (1 − e^{−x}) x^{−1} ∑ p_i² ≤ p`. -/
theorem theorem_9_a {n : ℕ} (hn : 0 < n) (p : Fin n → ℝ) (hp : ∀ i, 0 < p i ∧ p i < 1) :
    MarkovChainCLT.tvDist (poissonBinomial p) (poissonMeasure (∑ i, p i).toNNReal) ≤
        (1 - Real.exp (-(∑ i, p i))) * (∑ i, p i)⁻¹ * ∑ i, p i ^ 2 ∧
      (1 - Real.exp (-(∑ i, p i))) * (∑ i, p i)⁻¹ * ∑ i, p i ^ 2 ≤ ⨆ i, p i := by sorry

end LargeCongestion.Poisson
