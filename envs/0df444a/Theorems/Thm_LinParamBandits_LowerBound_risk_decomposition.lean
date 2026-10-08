-- Prove2me | Theorems.Thm_LinParamBandits_LowerBound_risk_decomposition
-- name    : LinParamBandits.LowerBound.risk_decomposition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:17:53.943448+00:00
-- url     : https://prove2.me/theorems/0e15a41e-c989-44a7-9dfa-b08e3925a126
-- title:
--   Lemma 2.2 — Risk(T, ψ) ≥ ½ Σ_k E[‖Z‖ Σ_t (U_t′S^k_T)² + (T/‖Z‖)((Z − Ẑ_T)′S^k_T)²]
-- statement:
--   Work in the model of Section 2: arms on the unit sphere of $\mathbb R^r$ ($r \ge 2$), prior $Z \sim N(0, I_r/r)$, standard normal noise, and a fixed policy $\psi$ with arms $U_1, U_2, \dots$. Let $\widehat Z_T = \mathbb E[Z \mid H_T]$, and let $S^1_T, \dots, S^{r-1}_T$ be orthonormal vectors, orthogonal to $\widehat Z_T$, each a measurable function of the history $H_T$.
--
--   **Lemma 2.2 (Risk Decomposition).** For any $T \ge 1$,
--   $$\mathrm{Risk}(T, \psi) \;\ge\; \frac12 \sum_{k=1}^{r-1} \mathbb E\left[\|Z\| \sum_{t=1}^T \big(U_t' S^k_T\big)^2 + \frac{T}{\|Z\|}\Big\{\big(Z - \widehat Z_T\big)' S^k_T\Big\}^2\right].$$
--
--   The first term inside the expectation measures how much the policy explored in the direction $S^k_T$, the second the squared estimation error in that direction; the lemma bounds the risk below by both.
--
--   **Formalization Note** The expectations on the right are lower Lebesgue integrals of nonnegative quantities, valued in $[0,\infty]$. On the event $Z = 0$, which has prior probability zero, Lean's convention $T/0 = 0$ applies. Orthogonality to $\widehat Z_T$ is required almost surely, since $\widehat Z_T$ is defined up to null sets; orthonormality is required for every history.
-- source:
--   Rusmevichientong, Tsitsiklis, Linearly Parameterized Bandits, arXiv:0812.3465v2, Lemma 2.2, p. 9; standing assumptions of Sec. 2, p. 9

import Mathlib
import Definitions.Def_LinParamBandits_LowerBound_Model

open MeasureTheory ProbabilityTheory

namespace LinParamBandits.LowerBound

/-- Lemma 2.2 (Risk Decomposition), Rusmevichientong, Tsitsiklis, arXiv:0812.3465v2, p. 9.
Standing assumptions of Sec. 2 (p. 9): arms on the unit sphere, prior `N(0, I_r/r)`; the vectors
`S k` (the paper's `S^1_T, …, S^{r-1}_T`) are orthonormal, orthogonal to `Ẑ_T`, and functions of
the history `H_T`. At `Z = 0` (prior probability zero) Lean's `T / 0 = 0`. -/
theorem risk_decomposition (r : ℕ) (hr : 2 ≤ r) (ψ : SpherePolicy r) (T : ℕ) (hT : 1 ≤ T)
    (S : Fin (r - 1) → History r T → Vec r)
    (hS_meas : ∀ k, Measurable (S k))
    (hS_orth : ∀ h, Orthonormal ℝ (fun k => S k h))
    (hS_perp : ∀ᵐ ω ∂(P r), ∀ k, inner ℝ (S k (hist ψ ω.1 ω.2 T)) (zhat ψ T ω) = 0) :
    2⁻¹ * ∑ k, ∫⁻ ω, ENNReal.ofReal
        (‖ω.1‖ * ∑ t ∈ Finset.range T, (inner ℝ (arm ψ ω.1 ω.2 t) (S k (hist ψ ω.1 ω.2 T))) ^ 2
          + (T : ℝ) / ‖ω.1‖ * (inner ℝ (ω.1 - zhat ψ T ω) (S k (hist ψ ω.1 ω.2 T))) ^ 2) ∂(P r)
      ≤ risk ψ T := by sorry

end LinParamBandits.LowerBound
