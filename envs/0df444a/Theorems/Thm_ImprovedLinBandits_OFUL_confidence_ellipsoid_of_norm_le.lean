-- Prove2me | Theorems.Thm_ImprovedLinBandits_OFUL_confidence_ellipsoid_of_norm_le
-- name    : ImprovedLinBandits.OFUL.confidence_ellipsoid_of_norm_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T17:21:36.209406+00:00
-- url     : https://prove2.me/theorems/65c8110c-968a-4dc7-927b-09ef8be285fe
-- title:
--   Theorem 2 (second claim) — confidence ellipsoid $C'_t$ for bounded actions
-- statement:
--   Assume the setting of Theorem 2 (first claim): a filtration, $F_{t-1}$-measurable actions $X_t \in \mathbb R^d$, $F_t$-measurable conditionally $R$-sub-Gaussian noise $\eta_t$, rewards $Y_t = \langle X_t, \theta_*\rangle + \eta_t$, $\|\theta_*\|_2 \le S$ and $\lambda > 0$. If moreover $\|X_t\|_2 \le L$ for all $t \ge 1$, then for every $\delta > 0$, with probability at least $1 - \delta$, for all $t \ge 0$, $\theta_*$ lies in
--
--   $$C'_t = \left\{\theta \in \mathbb R^d : \left\|\widehat\theta_t - \theta\right\|_{\overline V_t} \le R\sqrt{d\log\left(\frac{1 + tL^2/\lambda}{\delta}\right)} + \lambda^{1/2} S\right\}.$$
--
--   The radius of $C'_t$ no longer involves a determinant and grows like $\sqrt{d \log t}$.
--
--   **Formalization Note** The dimension is assumed to satisfy $d \ge 2$, which the paper does not state. The paper's proof (Appendix B) is not in the source file, and at $d = 1$ the claim does not follow from the first claim together with $\det \overline V_t \le (\lambda + tL^2/d)^d$, because $2\log(1/\delta) > \log(1/\delta)$ for $\delta < 1$. The outer probability of the failure event, with time inside the event, is bounded by $\delta$. `StandardBorelSpace` $\Omega$ is added as in Theorem 1.
-- source:
--   Abbasi-Yadkori, Pál, Szepesvári, Improved Algorithms for Linear Stochastic Bandits, NIPS 2011, p. 4, Theorem 2 (second claim, the set $C'_t$)

import Mathlib
import Definitions.Def_SelfNormalizedProcess

open MeasureTheory ProbabilityTheory Matrix NNReal

namespace ImprovedLinBandits.OFUL

/-- **Theorem 2, second claim** (Abbasi-Yadkori, Pál, Szepesvári, NIPS 2011, p. 4). Under the
assumptions of the first claim, if moreover `‖X_t‖₂ ≤ L` for all `t ≥ 1`, then for any `δ > 0` the
event that for some `t ≥ 0`
`‖θ̂_t - θ*‖_{V̄_t} > R √(d log((1 + t L²/λ)/δ)) + λ^{1/2} S`
has (outer) probability at most `δ`. The hypothesis `2 ≤ d` is added: the paper's proof is not in
the held text, and at `d = 1` the claim does not follow from the first claim. -/
theorem confidence_ellipsoid_of_norm_le
    {Ω : Type} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {d : ℕ} (ℱ : Filtration ℕ mΩ)
    (X : ℕ → Ω → Fin d → ℝ) (η : ℕ → Ω → ℝ) (Y : ℕ → Ω → ℝ) (θstar : Fin d → ℝ)
    (R : ℝ≥0) {S lam L δ : ℝ}
    (hd : 2 ≤ d)
    (hX : ∀ t : ℕ, Measurable[ℱ t] (X (t + 1)))
    (hη : ∀ t : ℕ, Measurable[ℱ (t + 1)] (η (t + 1)))
    (hsg : ∀ t : ℕ, HasCondSubgaussianMGF (ℱ t) (ℱ.le t) (η (t + 1)) (R ^ 2) P)
    (hY : ∀ (t : ℕ) (ω : Ω), Y (t + 1) ω = X (t + 1) ω ⬝ᵥ θstar + η (t + 1) ω)
    (hS : Real.sqrt (θstar ⬝ᵥ θstar) ≤ S)
    (hL : ∀ (t : ℕ) (ω : Ω), Real.sqrt (X (t + 1) ω ⬝ᵥ X (t + 1) ω) ≤ L)
    (hlam : 0 < lam) (hδ : 0 < δ) :
    P {ω | ∃ t : ℕ,
        (R : ℝ) * Real.sqrt ((d : ℝ) * Real.log ((1 + (t : ℝ) * L ^ 2 / lam) / δ))
            + Real.sqrt lam * S
          < Real.sqrt ((BanditAlgorithm.regularizedLeastSquares d lam X Y t ω - θstar) ⬝ᵥ
              BanditAlgorithm.regularizedDesignMatrix d lam X t ω *ᵥ
                (BanditAlgorithm.regularizedLeastSquares d lam X Y t ω - θstar))}
      ≤ ENNReal.ofReal δ := by sorry

end ImprovedLinBandits.OFUL
