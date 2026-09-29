-- Prove2me | Theorems.Thm_ImprovedLinBandits_OFUL_confidence_ellipsoid
-- name    : ImprovedLinBandits.OFUL.confidence_ellipsoid
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T17:21:18.505345+00:00
-- url     : https://prove2.me/theorems/250b9d39-47c2-4b01-9d3e-66ad5c74ec17
-- title:
--   Theorem 2 (first claim) — confidence ellipsoid $C_t$
-- statement:
--   Assume the setting of Theorem 1 with $V = \lambda I$, $\lambda > 0$: a filtration $\{F_t\}$, actions $X_t$ that are $F_{t-1}$-measurable, and noise $\eta_t$ that is $F_t$-measurable and conditionally $R$-sub-Gaussian given $F_{t-1}$. Let the rewards be $Y_t = \langle X_t, \theta_* \rangle + \eta_t$ for a parameter $\theta_* \in \mathbb R^d$ with $\|\theta_*\|_2 \le S$. Then for every $\delta > 0$, with probability at least $1 - \delta$, for all $t \ge 0$, $\theta_*$ lies in
--
--   $$C_t = \left\{\theta \in \mathbb R^d : \left\|\widehat\theta_t - \theta\right\|_{\overline V_t} \le R\sqrt{2\log\left(\frac{\det(\overline V_t)^{1/2}\det(\lambda I)^{-1/2}}{\delta}\right)} + \lambda^{1/2} S\right\},$$
--
--   where $\widehat\theta_t$ is the $\lambda$-regularized least-squares estimate from the first $t$ rounds and $\overline V_t = \lambda I + \sum_{s \le t} X_s X_s^\top$.
--
--   These are the confidence sets with which the OFUL algorithm is run in Theorem 3.
--
--   **Formalization Note** The outer probability of the failure event "$\theta_* \notin C_t$ for some $t$" is bounded by $\delta$; the time quantifier is inside the event. The platform row `BanditAlgorithm.least_squares_confidence_ellipsoid` is the special case $R = 1$, $S = \|\theta_*\|_2$, $\delta < 1$, stated with `P.real`. `StandardBorelSpace` $\Omega$ is added as in Theorem 1.
-- source:
--   Abbasi-Yadkori, Pál, Szepesvári, Improved Algorithms for Linear Stochastic Bandits, NIPS 2011, p. 4, Theorem 2 (first claim)

import Mathlib
import Definitions.Def_SelfNormalizedProcess
import Definitions.Def_ImprovedLinBandits_OFUL_confidenceSet

open MeasureTheory ProbabilityTheory Matrix NNReal

namespace ImprovedLinBandits.OFUL

/-- **Theorem 2, first claim** (Confidence Ellipsoid; Abbasi-Yadkori, Pál, Szepesvári, NIPS 2011,
p. 4). Under the assumptions of Theorem 1 with `V = λI`, `λ > 0`, rewards
`Y_{t+1} = ⟨X_{t+1}, θ*⟩ + η_{t+1}` and `‖θ*‖₂ ≤ S`, for any `δ > 0` the event that `θ* ∉ C_t` for
some `t ≥ 0` has (outer) probability at most `δ`. -/
theorem confidence_ellipsoid
    {Ω : Type} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {d : ℕ} (ℱ : Filtration ℕ mΩ)
    (X : ℕ → Ω → Fin d → ℝ) (η : ℕ → Ω → ℝ) (Y : ℕ → Ω → ℝ) (θstar : Fin d → ℝ)
    (R : ℝ≥0) {S lam δ : ℝ}
    (hX : ∀ t : ℕ, Measurable[ℱ t] (X (t + 1)))
    (hη : ∀ t : ℕ, Measurable[ℱ (t + 1)] (η (t + 1)))
    (hsg : ∀ t : ℕ, HasCondSubgaussianMGF (ℱ t) (ℱ.le t) (η (t + 1)) (R ^ 2) P)
    (hY : ∀ (t : ℕ) (ω : Ω), Y (t + 1) ω = X (t + 1) ω ⬝ᵥ θstar + η (t + 1) ω)
    (hS : Real.sqrt (θstar ⬝ᵥ θstar) ≤ S)
    (hlam : 0 < lam) (hδ : 0 < δ) :
    P {ω | ∃ t : ℕ, θstar ∉ confidenceSet d R S lam δ X Y t ω} ≤ ENNReal.ofReal δ := by sorry

end ImprovedLinBandits.OFUL
