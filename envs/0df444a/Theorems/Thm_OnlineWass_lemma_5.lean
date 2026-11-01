-- Prove2me | Theorems.Thm_OnlineWass_lemma_5
-- name    : OnlineWass.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:17:49.514603+00:00
-- url     : https://prove2.me/theorems/ae693e4f-dea1-4b41-9f48-da8ed2d7d004
-- title:
--   Lemma 5 — (30) for every maximizer, (31) and (9) for a plan (corrected: complementary tie-break)
-- statement:
--   For each $t$ let
--
--   $$
--   \hat L_t(p)=\hat\gamma_t^\top p+\hat{\mathcal P}_t h(p;\theta),\qquad \hat\gamma_t=\hat{\mathcal P}_t g(\hat x(\theta);\theta).
--   $$
--
--   1. If $\hat p^*\ge0$ and $\hat x(\theta)$ is a measurable maximizer of $f(x;\theta)-(\hat p^*)^\top g(x;\theta)$ over $\mathcal X$ (any tie-break), then $\hat p^*\in\operatorname{argmin}_{p\ge0}\hat L_t(p)$ for each $t$ (30).
--   2. If $(\hat p^*,\hat x)$ is a fluid plan, then $\hat L(\hat p^*)=\sum_{t=1}^T\hat L_t(\hat p^*)$ (31) and $\hat p^*\in\operatorname{argmin}_{p\ge0}\hat L(p)$ (9).
--
--   All the period-wise dual functions share one minimizer, which lets a single price sequence track all of them.
--
--   Differences from the source:
--   - correction: (31) with x̂ from (10), any maximizer → (31) for a fluid plan (IsFluidPlan: x̂ a measurable maximizer with Σₜγ̂ₜ ≤ c and (p̂*)ᵀ(c − Σₜγ̂ₜ) = 0); reason: with a free tie-break the bound fails: Θ={a,b}, f(x;a)=x/2, f(x;b)=x, g=x, 𝒳=[0,1], q=1, c=3T/4, θₜ=a for t≤T/2 else b, 𝒫̂=𝒫, W_T=0, x̂(a)=1 gives regret T/8; every minimizer has a complementary x̂ (exists_fluid_plan), and when the argmax is unique it is the printed x̂
--   - generalization: (30) for p̂* satisfying (9) → (30) for every p̂* ≥ 0 with any measurable maximizer x̂; reason: the proof of (30) uses only that x̂(θ) maximizes the Lagrangian
--   - generalization: Θ ⊂ ℝˡ → Θ any metric Borel space with distance (2); reason: ρ is the only structure the paper uses on Θ; a subset of ℝˡ with ρ is an instance
--   - encoding: p̂* assumed to satisfy (9) → (9) a conclusion from the clauses of IsFluidPlan; reason: a plan satisfies (9), so the hypotheses agree
--   - encoding: min over p ≥ 0 → an inequality at each p ≥ 0; reason: definition of argmin
-- source:
--   Jiang, Li & Zhang, Online Stochastic Optimization with Wasserstein Based Non-stationarity, arXiv:2012.06961v3, Lemma 5, (29)–(31), p.55; (9), p.21

import Mathlib
import Definitions.Def_OnlineWass_Model
import Definitions.Def_OnlineWass_dual
import Definitions.Def_OnlineWass_IsFluidPlan

open MeasureTheory

namespace OnlineWass

/-- **Lemma 5, Jiang, Li & Zhang, arXiv:2012.06961v3, p.55, corrected.** With
`L̂ₜ(p) := γ̂ₜᵀp + 𝒫̂ₜh(p; θ)` of (29) and `γ̂ₜ := 𝒫̂ₜ g(x̂(θ); θ)`:
(30) if `p̂* ≥ 0` and `x̂(θ)` is a measurable maximizer of `f(x; θ) − (p̂*)ᵀg(x; θ)` over `𝒳` (any tie-break),
then `p̂* ∈ argmin_{p≥0} L̂ₜ(p)` for each `t`; and if `(p̂*, x̂)` is a plan, then (31) `L̂(p̂*) = Σₜ L̂ₜ(p̂*)` and
(9) `p̂* ∈ argmin_{p≥0} L̂(p)`.

**Formalization Note.** The printed lemma assumes (9) and leaves the tie-break of (10) free. (30) holds for
every maximizer and every `p̂* ≥ 0`, so it is stated so; under a free tie-break (31) fails, so it is stated for
a plan, and (9) is then a conclusion. -/
theorem lemma_5 {k m T : ℕ} {Θ : Type*} [MetricSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    (M : Model k m Θ) (hA : Assumption1ab M) (hρ : DistEqRho M) (hT : 0 < T) (c : Fin m → ℝ)
    (Phat : Fin T → Measure Θ) [∀ t, IsProbabilityMeasure (Phat t)]
    (phat : Fin m → ℝ) (xhat : Θ → Fin k → ℝ) :
    (0 ≤ phat → Measurable xhat → (∀ θ, xhat θ ∈ M.X) →
      (∀ θ, IsMaxOn (fun x => M.lagrangian phat x θ) M.X (xhat θ)) →
      ∀ (t : Fin T) (p : Fin m → ℝ), 0 ≤ p →
        ∑ i, gammaHat M Phat xhat t i * phat i + LQ M (Phat t) phat ≤
          ∑ i, gammaHat M Phat xhat t i * p i + LQ M (Phat t) p) ∧
    (IsFluidPlan M c Phat phat xhat →
      dual M c Phat phat = ∑ t, (∑ i, gammaHat M Phat xhat t i * phat i + LQ M (Phat t) phat) ∧
      IsDualMinimizer M c Phat phat) := by sorry

end OnlineWass
