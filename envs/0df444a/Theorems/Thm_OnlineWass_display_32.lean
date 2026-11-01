-- Prove2me | Theorems.Thm_OnlineWass_display_32
-- name    : OnlineWass.display_32
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:18:13.790427+00:00
-- url     : https://prove2.me/theorems/302bfd52-e874-4d4a-8b0c-d0704e3ccd67
-- title:
--   (32) — the dual term I (corrected: $f(0;\theta)\ge0$, complementary tie-break)
-- statement:
--   Under Assumption 1 with $\rho$ of (2) as the distance of $\Theta$, $f(0;\theta)\ge0$ and $c\ge0$, let $(\hat p^*,\hat x)$ be a fluid plan for the prior $\hat{\mathcal P}$, $\mathrm{sel}$ a tie-break rule, and $\mathcal P$ a law with $\sum_t\mathcal W(\mathcal P_t,\hat{\mathcal P}_t)\le W_T$. With $p'=\hat p^*\wedge q$, for the run of IGD($\hat\gamma$) under $\theta_t\sim\mathcal P_t$ independent,
--
--   $$
--   L(p')-\mathbb E\Bigl[\sum_{t=1}^T f(\tilde x_t;\theta_t)\Bigr]\le\frac{m\sqrt T}2+2(q+1)(m+1)\,W_T.
--   $$
--
--   This is where the deviation budget appears, at the two uses of Lemma 3.
--
--   Differences from the source:
--   - correction: Assumption 1 says nothing on f(0;θ); the proofs treat x = 0 as having zero objective value → separate hypothesis f(0;θ) ≥ 0 for every θ; reason: Theorem 3 fails: 𝒳=[0,1], m=1, q=1, Θ a point, W_T=0, g(x)=x, f(x)=−(1−Tx)² on [0,1/T] and 0 beyond, c=1/2 satisfies Assumption 1 and has regret ≈ T/4
--   - correction: (10) writes x̂(θ) = argmax, any maximizer → IsFluidPlan: x̂ a measurable maximizer with Σₜγ̂ₜ ≤ c and (p̂*)ᵀ(c − Σₜγ̂ₜ) = 0; reason: with a free tie-break the bound fails: Θ={a,b}, f(x;a)=x/2, f(x;b)=x, g=x, 𝒳=[0,1], q=1, c=3T/4, θₜ=a for t≤T/2 else b, 𝒫̂=𝒫, W_T=0, x̂(a)=1 gives regret T/8; every minimizer has a complementary x̂ (exists_fluid_plan), and when the argmax is unique it is the printed x̂
--   - generalization: Θ ⊂ ℝˡ → Θ any metric Borel space with distance (2); reason: ρ is the only structure the paper uses on Θ; a subset of ℝˡ with ρ is an instance
--   - generalization: initial capacity c, sign unstated → every c ≥ 0, including cᵢ = 0; reason: at cᵢ < 0 (PCP) is infeasible; the source's c is a case
--   - generalization: x̃ₜ = argmax with no rule for ties → any jointly measurable tie-break rule sel; reason: every solver of line 4 that reads (pₜ, θₜ) is such a rule, and the bound holds for each
--   - encoding: I = min_{p≥0} L(p) − E[…], with p̂* in Bound I → L(p′) − E[…] at p′ = p̂* ∧ q; reason: L(p′) ≥ min_{p≥0} L(p), so this implies the printed form; for c > 0, p′ = p̂* by plan_price_bound
--   - encoding: W_T = Σₜ 𝒲(𝒫ₜ, 𝒫̂ₜ) → any W_T ≥ 0 above that sum; reason: the budget of Ξ_P(W_T)
-- source:
--   Jiang, Li & Zhang, Online Stochastic Optimization with Wasserstein Based Non-stationarity, arXiv:2012.06961v3, (32), p.56

import Mathlib
import Definitions.Def_OnlineWass_Model
import Definitions.Def_OnlineWass_wasserstein
import Definitions.Def_OnlineWass_dual
import Definitions.Def_OnlineWass_IsFluidPlan
import Definitions.Def_OnlineWass_igd

open MeasureTheory

namespace OnlineWass

open scoped ENNReal in
/-- **(32), Jiang, Li & Zhang, arXiv:2012.06961v3, p.56, for a plan:** with `p' = p̂* ∧ q`,
`L(p') − 𝔼[Σₜ f(x̃ₜ; θₜ)] ≤ m√T/2 + 2(q + 1)(m + 1) W_T`, whenever `Σₜ 𝒲(𝒫ₜ, 𝒫̂ₜ) ≤ W_T`.

**Formalization Note.** The printed `I` has `min_{p≥0} L(p)`, and `L(p') ≥ min_{p≥0} L(p)`, so this
is at least as strong; for `c > 0`, `p' = p̂*` by `OnlineWass.plan_price_bound`. -/
theorem display_32 {k m T : ℕ} {Θ : Type*} [MetricSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    (M : Model k m Θ) (q : ℝ) (hA : Assumption1 M q) (hρ : DistEqRho M)
    (hf0 : ∀ θ, 0 ≤ M.f 0 θ) (hT : 0 < T) (c : Fin m → ℝ) (hc : 0 ≤ c)
    (Phat : Fin T → Measure Θ) [∀ t, IsProbabilityMeasure (Phat t)]
    (phat : Fin m → ℝ) (xhat : Θ → Fin k → ℝ) (hplan : IsFluidPlan M c Phat phat xhat)
    (sel : (Fin m → ℝ) → Θ → Fin k → ℝ) (hsel : IsTieBreak M sel)
    (P : Fin T → Measure Θ) [∀ t, IsProbabilityMeasure (P t)]
    (WT : ℝ) (hWT : 0 ≤ WT) (hW : deviationBudget P Phat ≤ ENNReal.ofReal WT) :
    dual M c P (fun i => min (phat i) q) -
        ∫ H, virtualReward M sel (gammaHat M Phat xhat) H ∂Measure.pi P ≤
      (m : ℝ) * √(T : ℝ) / 2 + 2 * (q + 1) * ((m : ℝ) + 1) * WT := by sorry

end OnlineWass
