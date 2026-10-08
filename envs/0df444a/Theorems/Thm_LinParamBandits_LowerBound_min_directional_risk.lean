-- Prove2me | Theorems.Thm_LinParamBandits_LowerBound_min_directional_risk
-- name    : LinParamBandits.LowerBound.min_directional_risk
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:18:02.952433+00:00
-- url     : https://prove2.me/theorems/ccd5f4be-bba5-4b19-9df0-f16a34a4f943
-- title:
--   Lemma 2.5 — E[‖Z‖ Σ_t (U_t′S^k_T)² + (T/‖Z‖)((Z − Ẑ_T)′S^k_T)²] ≥ 0.027√T for T ≥ r²
-- statement:
--   Work in the model of Section 2 with the vectors $S^1_T, \dots, S^{r-1}_T$ of Lemma 2.2 (orthonormal, orthogonal to $\widehat Z_T = \mathbb E[Z \mid H_T]$, measurable functions of $H_T$).
--
--   **Lemma 2.5 (Minimum Directional Risk).** For $k = 1, \dots, r-1$ and $T \ge r^2$,
--   $$\mathbb E\left[\|Z\| \sum_{t=1}^T \big(U_t' S^k_T\big)^2 + \frac{T}{\|Z\|}\Big\{\big(Z - \widehat Z_T\big)' S^k_T\Big\}^2\right] \;\ge\; 0.027\sqrt T.$$
--
--   By Lemma 2.2 the left-hand side is (twice) the minimal cumulative Bayes risk along the direction $S^k_T$; summing over the $r - 1$ directions gives Theorem 2.1.
--
--   **Formalization Note** The expectation is a lower Lebesgue integral of a nonnegative quantity, valued in $[0, \infty]$; on the null event $Z = 0$ Lean's $T/0 = 0$ applies. The constant $0.027$ is the paper's.
-- source:
--   Rusmevichientong, Tsitsiklis, Linearly Parameterized Bandits, arXiv:0812.3465v2, Lemma 2.5, p. 11 (proof pp. 11–13); standing assumptions of Sec. 2, p. 9

import Mathlib
import Definitions.Def_LinParamBandits_LowerBound_Model

open MeasureTheory ProbabilityTheory

namespace LinParamBandits.LowerBound

/-- Lemma 2.5 (Minimum Directional Risk), Rusmevichientong, Tsitsiklis, arXiv:0812.3465v2, p. 11:
for each direction `k` and `T ≥ r²`,
`E[‖Z‖ ∑_{t=1}^T (U_t′ S^k_T)² + (T/‖Z‖) ((Z − Ẑ_T)′ S^k_T)²] ≥ 0.027 √T`.
Standing assumptions of Sec. 2 (p. 9) as in Lemma 2.2. -/
theorem min_directional_risk (r : ℕ) (hr : 2 ≤ r) (ψ : SpherePolicy r) (T : ℕ) (hT : r ^ 2 ≤ T)
    (S : Fin (r - 1) → History r T → Vec r)
    (hS_meas : ∀ k, Measurable (S k))
    (hS_orth : ∀ h, Orthonormal ℝ (fun k => S k h))
    (hS_perp : ∀ᵐ ω ∂(P r), ∀ k, inner ℝ (S k (hist ψ ω.1 ω.2 T)) (zhat ψ T ω) = 0)
    (k : Fin (r - 1)) :
    ENNReal.ofReal (0.027 * Real.sqrt T)
      ≤ ∫⁻ ω, ENNReal.ofReal
          (‖ω.1‖ * ∑ t ∈ Finset.range T, (inner ℝ (arm ψ ω.1 ω.2 t) (S k (hist ψ ω.1 ω.2 T))) ^ 2
            + (T : ℝ) / ‖ω.1‖ * (inner ℝ (ω.1 - zhat ψ T ω) (S k (hist ψ ω.1 ω.2 T))) ^ 2) ∂(P r) := by sorry

end LinParamBandits.LowerBound
