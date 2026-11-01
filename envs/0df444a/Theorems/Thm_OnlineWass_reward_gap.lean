-- Prove2me | Theorems.Thm_OnlineWass_reward_gap
-- name    : OnlineWass.reward_gap
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:17:23.172026+00:00
-- url     : https://prove2.me/theorems/e2771208-1f41-42d0-807d-9c193e075047
-- title:
--   Reward gap of the virtual actions (corrected: $f(0;\theta)\ge0$)
-- statement:
--   Under Assumption 1 with $f(0;\theta)\ge0$, for $c\ge0$, any input $\gamma$, any tie-break rule and every profile,
--
--   $$
--   \sum_{t=1}^T f(\tilde x_t;\theta_t)-\sum_{t=1}^T f(x_t;\theta_t)\le q\sum_{i=1}^m\sum_{t=1}^T g_i(\tilde x_t;\theta_t)\,\mathbb I\Bigl\{\sum_{j=1}^t g_i(\tilde x_j;\theta_j)>c_i\Bigr\}\le q\sum_{i=1}^m\Bigl[\sum_{t=1}^T g_i(\tilde x_t;\theta_t)-(c_i-1)\Bigr]^+.
--   $$
--
--   It relates the reward of the true actions to that of the virtual actions: a period is lost only after some constraint has been overrun.
--
--   Differences from the source:
--   - correction: Assumption 1 says nothing on f(0;θ); the proof uses f(x̃ₜ;θₜ) − f(0;θₜ) ≤ f(x̃ₜ;θₜ) → separate hypothesis f(0;θ) ≥ 0 for every θ; reason: with f(0;θ) < 0 a blocked period costs more than f(x̃ₜ;θₜ): 𝒳=[0,1], m=1, q=1, Θ a point, g(x)=x, f(x)=−(1−Tx)² on [0,1/T] and 0 beyond, c=1/2 gives a regret ≈ T/4
--   - generalization: initial capacity c, sign unstated → every c ≥ 0, including cᵢ = 0; reason: at cᵢ < 0 (PCP) is infeasible; the source's c is a case
--   - generalization: x̃ₜ = argmax with no rule for ties → any jointly measurable tie-break rule sel; reason: every solver of line 4 that reads (pₜ, θₜ) is such a rule, and the bound holds for each
--   - generalization: run of IGD(γ̂) → any input γ; reason: the input plays no part in the bound
--   - encoding: periods t = 1, …, T, p₁, p_{T+1} → t : Fin T is period t + 1; p₁ is index 0, p_{T+1} is index T; reason: Lean indices; same instances
-- source:
--   Jiang, Li & Zhang, Online Stochastic Optimization with Wasserstein Based Non-stationarity, arXiv:2012.06961v3, Proof of Theorem 1, p.48; proof of Theorem 3, p.55

import Mathlib
import Definitions.Def_OnlineWass_Model
import Definitions.Def_OnlineWass_igd

open MeasureTheory

namespace OnlineWass

/-- **The reward gap, Jiang, Li & Zhang, arXiv:2012.06961v3, p.48 (Theorem 1's proof) and p.55 (Theorem 3's
proof):** on every profile `H`,
`Σₜ f(x̃ₜ; θₜ) − Σₜ f(xₜ; θₜ) ≤ q Σᵢ Σₜ gᵢ(x̃ₜ; θₜ) 𝕀{Σ_{j≤t} gᵢ(x̃ⱼ; θⱼ) > cᵢ} ≤ q Σᵢ [Σₜ gᵢ(x̃ₜ; θₜ) − (cᵢ − 1)]⁺`.

**Formalization Note.** The sum in the indicator is over the virtual actions, while the capacity of the
run is depleted by the true ones. The input `γ` is arbitrary, as the bound does not use it. -/
theorem reward_gap {k m T : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    (M : Model k m Θ) (q : ℝ) (hA : Assumption1 M q)
    (hf0 : ∀ θ, 0 ≤ M.f 0 θ) (c : Fin m → ℝ) (hc : 0 ≤ c) (γ : Fin T → Fin m → ℝ)
    (sel : (Fin m → ℝ) → Θ → Fin k → ℝ) (hsel : IsTieBreak M sel) (H : Fin T → Θ) :
    virtualReward M sel γ H - onlineReward M sel γ c H ≤
        q * ∑ i, ∑ t, M.g (virtualAction M sel γ H t) (H t) i *
          (if c i < ∑ j ∈ Finset.Iic t, M.g (virtualAction M sel γ H j) (H j) i then 1 else 0) ∧
      q * (∑ i, ∑ t, M.g (virtualAction M sel γ H t) (H t) i *
          (if c i < ∑ j ∈ Finset.Iic t, M.g (virtualAction M sel γ H j) (H j) i then 1 else 0)) ≤
        q * overshoot M sel γ c H := by sorry

end OnlineWass
