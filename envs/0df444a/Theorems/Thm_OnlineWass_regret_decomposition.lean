-- Prove2me | Theorems.Thm_OnlineWass_regret_decomposition
-- name    : OnlineWass.regret_decomposition
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:17:35.785199+00:00
-- url     : https://prove2.me/theorems/41283cac-b3d3-4dde-91c3-1afd70ec9a30
-- title:
--   Regret decomposition (corrected: $f(0;\theta)\ge0$)
-- statement:
--   Under Assumption 1 with $\rho$ of (2) as the distance of $\Theta$ and $f(0;\theta)\ge0$, for $c\ge0$, any input, any tie-break rule, every $p\ge0$ and independent $\theta_t\sim\mathcal P_t$,
--
--   $$
--   \mathbb E[R^*_T]-\mathbb E\Bigl[\sum_t f(x_t;\theta_t)\Bigr]\le L(p)-\mathbb E\Bigl[\sum_t f(x_t;\theta_t)\Bigr]\le L(p)-\mathbb E\Bigl[\sum_t f(\tilde x_t;\theta_t)\Bigr]+q\,\mathbb E\Bigl[\sum_{i=1}^m\Bigl[\sum_t g_i(\tilde x_t;\theta_t)-(c_i-1)\Bigr]^+\Bigr].
--   $$
--
--   This splits the regret into the terms I and II of the proof of Theorem 3.
--
--   **Formalization Note** The printed minimum over $p\ge0$ is the statement for every $p\ge0$: the proof needs it at a chosen $p$. The integrands are integrable by `OnlineWass.regret_wellDefined`.
--
--   Differences from the source:
--   - correction: Assumption 1 says nothing on f(0;θ); the proof uses f(x̃ₜ;θₜ) − f(0;θₜ) ≤ f(x̃ₜ;θₜ) → separate hypothesis f(0;θ) ≥ 0 for every θ; reason: with f(0;θ) < 0 a blocked period costs more than f(x̃ₜ;θₜ): 𝒳=[0,1], m=1, q=1, Θ a point, g(x)=x, f(x)=−(1−Tx)² on [0,1/T] and 0 beyond, c=1/2 gives a regret ≈ T/4
--   - generalization: Θ ⊂ ℝˡ → Θ any metric Borel space with distance (2); reason: ρ is the only structure the paper uses on Θ; a subset of ℝˡ with ρ is an instance
--   - generalization: initial capacity c, sign unstated → every c ≥ 0, including cᵢ = 0; reason: at cᵢ < 0 (PCP) is infeasible; the source's c is a case
--   - generalization: x̃ₜ = argmax with no rule for ties → any jointly measurable tie-break rule sel; reason: every solver of line 4 that reads (pₜ, θₜ) is such a rule, and the bound holds for each
--   - encoding: min_{p≥0} L(p) → for every p ≥ 0; reason: the bound at every p gives the bound at the minimum, and the proof picks p′ = p̂* ∧ q
-- source:
--   Jiang, Li & Zhang, Online Stochastic Optimization with Wasserstein Based Non-stationarity, arXiv:2012.06961v3, Proof of Theorem 3, p.56, first display

import Mathlib
import Definitions.Def_OnlineWass_Model
import Definitions.Def_OnlineWass_dual
import Definitions.Def_OnlineWass_igd
import Definitions.Def_OnlineWass_benchmarks

open MeasureTheory

namespace OnlineWass

/-- **The regret decomposition, Jiang, Li & Zhang, arXiv:2012.06961v3, p.56, first display.** For every
`p ≥ 0`, `𝔼[R*_T] − 𝔼[Σₜ f(xₜ; θₜ)] ≤ L(p) − 𝔼[Σₜ f(xₜ; θₜ)]
≤ L(p) − 𝔼[Σₜ f(x̃ₜ; θₜ)] + q 𝔼[Σᵢ [Σₜ gᵢ(x̃ₜ; θₜ) − (cᵢ − 1)]⁺]`.

**Formalization Note.** The printed `min_{p≥0}` is `∀ p ≥ 0`. All integrands are integrable by
`OnlineWass.regret_wellDefined`. -/
theorem regret_decomposition {k m T : ℕ} {Θ : Type*} [MetricSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    (M : Model k m Θ) (q : ℝ) (hA : Assumption1 M q) (hρ : DistEqRho M)
    (hf0 : ∀ θ, 0 ≤ M.f 0 θ) (hT : 0 < T) (c : Fin m → ℝ) (hc : 0 ≤ c) (γ : Fin T → Fin m → ℝ)
    (sel : (Fin m → ℝ) → Θ → Fin k → ℝ) (hsel : IsTieBreak M sel)
    (P : Fin T → Measure Θ) [∀ t, IsProbabilityMeasure (P t)]
    (p : Fin m → ℝ) (hp : 0 ≤ p) :
    ∫ H, offlineValue M c H ∂Measure.pi P - ∫ H, onlineReward M sel γ c H ∂Measure.pi P ≤
        dual M c P p - ∫ H, onlineReward M sel γ c H ∂Measure.pi P ∧
      dual M c P p - ∫ H, onlineReward M sel γ c H ∂Measure.pi P ≤
        dual M c P p - ∫ H, virtualReward M sel γ H ∂Measure.pi P +
          q * ∫ H, overshoot M sel γ c H ∂Measure.pi P := by sorry

end OnlineWass
