-- Prove2me | Theorems.Thm_LandauCriterion_psi_oscillation_of_not_riemannHypothesis
-- name    : LandauCriterion.psi_oscillation_of_not_riemannHypothesis
-- status  : Open
-- author  : @pitimespi
-- created : 2026-11-01T18:53:39.746854+00:00
-- url     : https://prove2.me/theorems/2590ad57-b67a-4135-acd1-607969eacd66
-- title:
--   Failure of the Riemann hypothesis forces psi-oscillation
-- statement:
--   Assume the Riemann hypothesis is false. Then there are real numbers $\beta > 1/2$ and $c > 0$ such that, for every $\varepsilon > 0$, the error $\psi(x) - x$ exceeds $c x^{\beta - \varepsilon}$ for arbitrarily large $x$ and also falls below $-c x^{\beta - \varepsilon}$ for arbitrarily large $x$. This is the classical $\Omega_{\pm}$ oscillation theorem: a zero off the critical line forces the prime distribution to oscillate on both sides of its main term at a power scale. This is the reverse analytic direction of the criterion.
-- source:
--   Landau's oscillation theorem for the Chebyshev function, as used in the classical proof of the Landau criterion; cf. Massias, Nicolas, Robin, Acta Arith. 50 (1988).

import Mathlib

namespace LandauCriterion
theorem psi_oscillation_of_not_riemannHypothesis (h : ¬ RiemannHypothesis) :
    ∃ β c : ℝ, 1 / 2 < β ∧ 0 < c ∧ ∀ ε : ℝ, 0 < ε →
      (Filter.Frequently (fun x : ℝ => c * x ^ (β - ε) ≤ Chebyshev.psi x - x) Filter.atTop) ∧
      (Filter.Frequently (fun x : ℝ => Chebyshev.psi x - x ≤ -c * x ^ (β - ε)) Filter.atTop) := by sorry
end LandauCriterion
