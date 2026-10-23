-- Prove2me | Theorems.Thm_LargeCongestion_Poisson_eq_46
-- name    : LargeCongestion.Poisson.eq_46
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:26:41.363389+00:00
-- url     : https://prove2.me/theorems/aa218c8b-85ae-423b-a540-cfa07367cd24
-- title:
--   (46), p. 37 — total variation between Poisson(x) and Poisson(y) is at most 1 − e^{−|x−y|} ≤ |x − y|
-- statement:
--   Let $x, y \ge 0$, $X \sim \mathrm{Poisson}(x)$ and $Y \sim \mathrm{Poisson}(y)$, and let $\rho_{TV}(\mathsf Q, \mathsf Q') = \sup_{A \subseteq \mathbb N}|\mathsf Q(A) - \mathsf Q'(A)|$ be the total variation distance (15). Then
--   $$\rho_{TV}(\mathcal L(X), \mathcal L(Y)) \le 1 - e^{-|x-y|} \le |x - y| .$$
--
--   Two Poisson laws with close means are close in total variation; this is how convergence of the means of flows and loads is turned into convergence of their laws in Proposition 1 and Theorem 2.
--
--   **Formalization Note** $\rho_{TV}$ is the published `MarkovChainCLT.tvDist`, the supremum over measurable sets, which on $\mathbb N$ is every set.
-- source:
--   Cominetti, Scarsini, Schröder & Stier-Moses, Approximation and Convergence of Large Atomic Congestion Games, arXiv:2001.02797v7, p. 37, Appendix C, (46)

import Mathlib
import Definitions.Def_TotalVariationDist
import Definitions.Def_LargeCongestion_Poisson_PoissonCalculus

namespace LargeCongestion.Poisson

open MeasureTheory ProbabilityTheory

/-- (46), Appendix C, p. 37: `ρ_TV(L(X), L(Y)) ≤ 1 − e^{−|x−y|} ≤ |x − y|` for
`X ∼ Poisson(x)`, `Y ∼ Poisson(y)`. -/
theorem eq_46 (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    MarkovChainCLT.tvDist (poissonMeasure x.toNNReal) (poissonMeasure y.toNNReal) ≤
        1 - Real.exp (-|x - y|) ∧
      1 - Real.exp (-|x - y|) ≤ |x - y| := by sorry

end LargeCongestion.Poisson
