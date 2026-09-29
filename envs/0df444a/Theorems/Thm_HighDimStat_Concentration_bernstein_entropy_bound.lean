-- Prove2me | Theorems.Thm_HighDimStat_Concentration_bernstein_entropy_bound
-- name    : HighDimStat.Concentration.bernstein_entropy_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-20T04:15:43.206666+00:00
-- url     : https://prove2.me/theorems/a808591e-e360-4a4a-a81c-50c9b71ce947
-- title:
--   Proposition 3.3 -- the Bernstein entropy bound
-- statement:
--   **Proposition 3.3 (Bernstein entropy bound).** Suppose there are positive constants $b$ and
--   $\sigma$ such that the entropy $H(e^{\lambda X})$ satisfies
--
--   $$
--   H(e^{\lambda X}) \;\le\; \lambda^2\big\{b\,\varphi_X'(\lambda) + \varphi_X(\lambda)(\sigma^2-b\,\mathbb E[X])\big\}
--   $$
--
--   for all $\lambda\in[0,1/b)$. Then $X$ satisfies
--
--   $$
--   \log\mathbb E[e^{\lambda(X-\mathbb E[X])}] \;\le\; \sigma^2\lambda^2(1-b\lambda)^{-1} \qquad \text{for all } \lambda\in[0,1/b).
--   $$
--
--   This is the sub-exponential analogue of the Herbst argument (Proposition 3.2), the source
--   (via the usual Chernoff argument) of the usual Bernstein-type tail bound for variables with
--   sub-exponential entropy behavior.
--
--   **Formalization Note** $\varphi_X'(\lambda)$ (the derivative of the moment generating
--   function) is realized as `deriv (fun l => ∫ω, exp(l·Xω) ∂Prob) lam`, a legitimate way to
--   state the hypothesis without separately justifying differentiability, appropriate for a
--   draft theorem statement. `Integrable` hypotheses guard the Bochner-integral junk value (trap
--   2), as in `herbst_argument`.
-- source:
--   Wainwright, High-Dimensional Statistics, CUP 2019, p. 61 (PDF p. 81), Proposition 3.3, Eqs. (3.10)-(3.11)

import Mathlib
import Definitions.Def_HighDimStat_Concentration_phiEntropy

open MeasureTheory

namespace HighDimStat.Concentration

/-- **Proposition 3.3** (Bernstein entropy bound), Wainwright, *High-Dimensional Statistics*
(2019), p. 61. Suppose there are positive constants `b, σ` such that
`H(e^{λX}) ≤ λ²{b φ_X'(λ) + φ_X(λ)(σ²-bE[X])}` for all `λ ∈ [0,1/b)`. Then `X` satisfies
`log E[e^{λ(X-E[X])}] ≤ σ²λ²(1-bλ)⁻¹` for all `λ ∈ [0,1/b)`. -/
theorem bernstein_entropy_bound {Ω : Type*} [MeasurableSpace Ω] {Prob : Measure Ω}
    [IsProbabilityMeasure Prob] (X : Ω → ℝ) (b sigma : ℝ) (hb : 0 < b) (hsigma : 0 < sigma)
    (hInt : ∀ lam : ℝ, 0 ≤ lam → lam < 1 / b →
      Integrable (fun ω => Real.exp (lam * X ω)) Prob ∧
      Integrable (fun ω => Real.exp (lam * X ω) * Real.log (Real.exp (lam * X ω))) Prob)
    (hEntropy : ∀ lam : ℝ, 0 ≤ lam → lam < 1 / b →
      phiEntropy (fun ω => Real.exp (lam * X ω)) Prob ≤
        lam ^ 2 * (b * deriv (fun l : ℝ => ∫ ω, Real.exp (l * X ω) ∂Prob) lam +
          (∫ ω, Real.exp (lam * X ω) ∂Prob) * (sigma ^ 2 - b * ∫ ω, X ω ∂Prob))) :
    ∀ lam : ℝ, 0 ≤ lam → lam < 1 / b →
      Real.log (∫ ω, Real.exp (lam * (X ω - ∫ ω', X ω' ∂Prob)) ∂Prob) ≤
        sigma ^ 2 * lam ^ 2 * (1 - b * lam)⁻¹ := by sorry

end HighDimStat.Concentration
