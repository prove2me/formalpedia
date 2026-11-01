-- Prove2me | Theorems.Thm_OnlineWass_plan_price_bound
-- name    : OnlineWass.plan_price_bound
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:17:58.436338+00:00
-- url     : https://prove2.me/theorems/2204a117-06bb-4176-afc5-a8031ffc825d
-- title:
--   "$\|\hat p^*\|_\infty\le q$" (corrected: $f(0;\theta)\ge0$, $c>0$ or truncation)
-- statement:
--   Under Assumption 1 with $f(0;\theta)\ge0$ and $c\ge0$, let $(\hat p^*,\hat x)$ be a fluid plan. Then
--
--   1. $(\hat p^*\wedge q,\hat x)$ is a fluid plan as well, where the minimum is taken in each coordinate;
--   2. if $c_i>0$ for every $i$, then $\hat p^*_i\le q$ for every $i$.
--
--   The truncated price is the one the proof of Theorem 3 uses. Its size is what fixes the constant in Lemma 3.
--
--   Differences from the source:
--   - correction: ‖p̂*‖∞ ≤ q → clause 1 (truncation is a plan) and clause 2 (the bound for c > 0); reason: false at cᵢ = 0: 𝒳=[0,1], m=1, f=g=x, q=1, c=0, p̂*=5 is a minimizer of L̂
--   - correction: Assumption 1 says nothing on f(0;θ); the proof uses f(x̃ₜ;θₜ) − f(0;θₜ) ≤ f(x̃ₜ;θₜ) → separate hypothesis f(0;θ) ≥ 0 for every θ; reason: with f(0;θ) < 0 a blocked period costs more than f(x̃ₜ;θₜ): 𝒳=[0,1], m=1, q=1, Θ a point, g(x)=x, f(x)=−(1−Tx)² on [0,1/T] and 0 beyond, c=1/2 gives a regret ≈ T/4
--   - generalization: Θ ⊂ ℝˡ → Θ any metric Borel space with distance (2); reason: ρ is the only structure the paper uses on Θ; a subset of ℝˡ with ρ is an instance
--   - generalization: initial capacity c, sign unstated → every c ≥ 0, including cᵢ = 0; reason: at cᵢ < 0 (PCP) is infeasible; the source's c is a case
-- source:
--   Jiang, Li & Zhang, Online Stochastic Optimization with Wasserstein Based Non-stationarity, arXiv:2012.06961v3, Proof of Theorem 3, p.56, "Note that ‖p̂∗‖∞ ≤ q"

import Mathlib
import Definitions.Def_OnlineWass_Model
import Definitions.Def_OnlineWass_IsFluidPlan

open MeasureTheory

namespace OnlineWass

/-- **Proof of Theorem 3, Jiang, Li & Zhang, arXiv:2012.06961v3, p.56, "Note that ‖p̂*‖∞ ≤ q", corrected.**
(i) If `(p̂*, x̂)` is a plan, then so is `(p̂* ∧ q, x̂)`. (ii) If `c > 0` in every coordinate, then
`p̂*ᵢ ≤ q` for every `i`.

**Formalization Note.** The printed claim is false at `cᵢ = 0`; clause (i) is what the proof needs for
`c ≥ 0`. -/
theorem plan_price_bound {k m T : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    (M : Model k m Θ) (q : ℝ) (hA : Assumption1 M q)
    (hf0 : ∀ θ, 0 ≤ M.f 0 θ) (c : Fin m → ℝ) (hc : 0 ≤ c)
    (Phat : Fin T → Measure Θ) [∀ t, IsProbabilityMeasure (Phat t)]
    (phat : Fin m → ℝ) (xhat : Θ → Fin k → ℝ) (hplan : IsFluidPlan M c Phat phat xhat) :
    IsFluidPlan M c Phat (fun i => min (phat i) q) xhat ∧
      ((∀ i, 0 < c i) → ∀ i, phat i ≤ q) := by sorry

end OnlineWass
