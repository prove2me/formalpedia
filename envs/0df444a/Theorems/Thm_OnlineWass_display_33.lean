-- Prove2me | Theorems.Thm_OnlineWass_display_33
-- name    : OnlineWass.display_33
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:18:04.456648+00:00
-- url     : https://prove2.me/theorems/8bd40b2c-29a6-4636-8dea-bcb6dc639504
-- title:
--   (33) — the overshoot term II (corrected: $f(0;\theta)\ge0$, complementary tie-break)
-- statement:
--   Under the hypotheses of (32), for any law $\mathcal P$,
--
--   $$
--   \mathrm{II}=q\,\mathbb E\Bigl[\sum_{i=1}^m\Bigl[\sum_{t=1}^T g_i(\tilde x_t;\theta_t)-(c_i-1)\Bigr]^+\Bigr]\le mq(q+1)\sqrt T+qm.
--   $$
--
--   The virtual consumption overruns the plan by at most $\sqrt T\,p_{T+1}$, and the plan fits the budget, so Lemma 4 at $T+1$ bounds the overshoot on every profile.
--
--   Differences from the source:
--   - correction: Assumption 1 says nothing on f(0;θ); the proofs treat x = 0 as having zero objective value → separate hypothesis f(0;θ) ≥ 0 for every θ; reason: Theorem 3 fails: 𝒳=[0,1], m=1, q=1, Θ a point, W_T=0, g(x)=x, f(x)=−(1−Tx)² on [0,1/T] and 0 beyond, c=1/2 satisfies Assumption 1 and has regret ≈ T/4
--   - correction: (10) writes x̂(θ) = argmax, any maximizer → IsFluidPlan: x̂ a measurable maximizer with Σₜγ̂ₜ ≤ c and (p̂*)ᵀ(c − Σₜγ̂ₜ) = 0; reason: with a free tie-break the bound fails: Θ={a,b}, f(x;a)=x/2, f(x;b)=x, g=x, 𝒳=[0,1], q=1, c=3T/4, θₜ=a for t≤T/2 else b, 𝒫̂=𝒫, W_T=0, x̂(a)=1 gives regret T/8; every minimizer has a complementary x̂ (exists_fluid_plan), and when the argmax is unique it is the printed x̂
--   - generalization: Θ ⊂ ℝˡ → Θ any metric Borel space with distance (2); reason: ρ is the only structure the paper uses on Θ; a subset of ℝˡ with ρ is an instance
--   - generalization: initial capacity c, sign unstated → every c ≥ 0, including cᵢ = 0; reason: at cᵢ < 0 (PCP) is infeasible; the source's c is a case
--   - generalization: x̃ₜ = argmax with no rule for ties → any jointly measurable tie-break rule sel; reason: every solver of line 4 that reads (pₜ, θₜ) is such a rule, and the bound holds for each
-- source:
--   Jiang, Li & Zhang, Online Stochastic Optimization with Wasserstein Based Non-stationarity, arXiv:2012.06961v3, (33), p.57

import Mathlib
import Definitions.Def_OnlineWass_Model
import Definitions.Def_OnlineWass_IsFluidPlan
import Definitions.Def_OnlineWass_igd

open MeasureTheory

namespace OnlineWass

/-- **(33), Jiang, Li & Zhang, arXiv:2012.06961v3, p.57, for a plan:**
`II = q 𝔼[Σᵢ [Σₜ gᵢ(x̃ₜ; θₜ) − (cᵢ − 1)]⁺] ≤ mq(q + 1)√T + qm`.

**Formalization Note.** The overshoot is integrable by `OnlineWass.regret_wellDefined`. -/
theorem display_33 {k m T : ℕ} {Θ : Type*} [MetricSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    (M : Model k m Θ) (q : ℝ) (hA : Assumption1 M q) (hρ : DistEqRho M)
    (hf0 : ∀ θ, 0 ≤ M.f 0 θ) (hT : 0 < T) (c : Fin m → ℝ) (hc : 0 ≤ c)
    (Phat : Fin T → Measure Θ) [∀ t, IsProbabilityMeasure (Phat t)]
    (phat : Fin m → ℝ) (xhat : Θ → Fin k → ℝ) (hplan : IsFluidPlan M c Phat phat xhat)
    (sel : (Fin m → ℝ) → Θ → Fin k → ℝ) (hsel : IsTieBreak M sel)
    (P : Fin T → Measure Θ) [∀ t, IsProbabilityMeasure (P t)] :
    q * ∫ H, overshoot M sel (gammaHat M Phat xhat) c H ∂Measure.pi P ≤
      (m : ℝ) * q * (q + 1) * √(T : ℝ) + q * (m : ℝ) := by sorry

end OnlineWass
