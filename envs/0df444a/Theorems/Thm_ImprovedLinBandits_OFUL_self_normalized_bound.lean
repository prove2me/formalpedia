-- Prove2me | Theorems.Thm_ImprovedLinBandits_OFUL_self_normalized_bound
-- name    : ImprovedLinBandits.OFUL.self_normalized_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T17:20:44.556576+00:00
-- url     : https://prove2.me/theorems/51f76917-1c07-4ba0-b263-fb2911e6a88d
-- title:
--   Theorem 1 — self-normalized bound for vector-valued martingales
-- statement:
--   Let $(\Omega, \mathcal F, P)$ be a probability space with a filtration $\{F_t\}_{t \ge 0}$. Let $\{\eta_t\}_{t \ge 1}$ be real random variables such that $\eta_t$ is $F_t$-measurable and conditionally $R$-sub-Gaussian for some $R \ge 0$:
--
--   $$\forall \lambda \in \mathbb R, \qquad \mathbf E\left[e^{\lambda \eta_t} \mid F_{t-1}\right] \le \exp\left(\frac{\lambda^2 R^2}{2}\right).$$
--
--   Let $\{X_t\}_{t \ge 1}$ be $\mathbb R^d$-valued with $X_t$ $F_{t-1}$-measurable, and let $V$ be a $d \times d$ positive definite matrix. For $t \ge 0$ put $\overline V_t = V + \sum_{s=1}^t X_s X_s^\top$ and $S_t = \sum_{s=1}^t \eta_s X_s$. Then for every $\delta > 0$, with probability at least $1 - \delta$, simultaneously for all $t \ge 0$,
--
--   $$\|S_t\|^2_{\overline V_t^{-1}} \le 2R^2 \log\left(\frac{\det(\overline V_t)^{1/2}\det(V)^{-1/2}}{\delta}\right).$$
--
--   The bound is uniform in time and holds for adaptively chosen $X_t$; it is the source of the confidence sets of Theorem 2.
--
--   **Formalization Note** The statement bounds the outer probability of the failure event "there is $t$ with $\|S_t\|^2_{\overline V_t^{-1}} > 2R^2 \log(\cdots)$" by $\delta$, so no measurability of that event is needed. Conditional sub-Gaussianity is Mathlib's `HasCondSubgaussianMGF` with variance proxy $R^2$, and `StandardBorelSpace` $\Omega$ is added so that it is available. Rounds are indexed $t+1$; $S_t$ is the platform's `selfNormalizedSum`. $V \succ 0$ makes every $\overline V_t$ positive definite, so Lean's inverse and both determinants are the genuine ones.
-- source:
--   Abbasi-Yadkori, Pál, Szepesvári, Improved Algorithms for Linear Stochastic Bandits, NIPS 2011, p. 4, Theorem 1

import Mathlib
import Definitions.Def_SelfNormalizedProcess
import Definitions.Def_ImprovedLinBandits_OFUL_gramMatrix

open MeasureTheory ProbabilityTheory Matrix NNReal

namespace ImprovedLinBandits.OFUL

/-- **Theorem 1** (Self-Normalized Bound for Vector-Valued Martingales; Abbasi-Yadkori, Pál,
Szepesvári, NIPS 2011, p. 4). Let `ℱ` be a filtration, `η_{t+1}` be `ℱ_{t+1}`-measurable and
conditionally `R`-sub-Gaussian given `ℱ_t` (Mathlib's variance proxy `R ^ 2`), `X_{t+1}` be
`ℱ_t`-measurable, and `V` positive definite. With `V̄_t = V + ∑_{s≤t} X_s X_sᵀ` and
`S_t = ∑_{s≤t} η_s X_s`, for any `δ > 0` the event that for some `t ≥ 0`
`‖S_t‖²_{V̄_t⁻¹} > 2R² log(det(V̄_t)^{1/2} det(V)^{-1/2} / δ)` has (outer) probability at most `δ`.
`StandardBorelSpace Ω` is added so that Mathlib's conditional sub-Gaussianity is available. -/
theorem self_normalized_bound
    {Ω : Type} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {d : ℕ} (ℱ : Filtration ℕ mΩ)
    (X : ℕ → Ω → Fin d → ℝ) (η : ℕ → Ω → ℝ) (R : ℝ≥0)
    (hX : ∀ t : ℕ, Measurable[ℱ t] (X (t + 1)))
    (hη : ∀ t : ℕ, Measurable[ℱ (t + 1)] (η (t + 1)))
    (hsg : ∀ t : ℕ, HasCondSubgaussianMGF (ℱ t) (ℱ.le t) (η (t + 1)) (R ^ 2) P)
    (V : Matrix (Fin d) (Fin d) ℝ) (hV : V.PosDef)
    {δ : ℝ} (hδ : 0 < δ) :
    P {ω | ∃ t : ℕ,
        2 * (R : ℝ) ^ 2 * Real.log
            (Real.sqrt (gramMatrix V X t ω).det * (Real.sqrt V.det)⁻¹ / δ)
          < BanditAlgorithm.selfNormalizedSum d η X t ω ⬝ᵥ
              (gramMatrix V X t ω)⁻¹ *ᵥ BanditAlgorithm.selfNormalizedSum d η X t ω}
      ≤ ENNReal.ofReal δ := by sorry

end ImprovedLinBandits.OFUL
