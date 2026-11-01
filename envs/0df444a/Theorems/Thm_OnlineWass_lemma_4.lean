-- Prove2me | Theorems.Thm_OnlineWass_lemma_4
-- name    : OnlineWass.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:18:20.319614+00:00
-- url     : https://prove2.me/theorems/c900fa50-dd32-4bca-94f0-10d2fa3973ed
-- title:
--   Lemma 4 — $\|p_t\|_\infty\le q+1$ (corrected: $f(0;\theta)\ge0$)
-- statement:
--   Under Assumption 1 with $f(0;\theta)\ge0$, let $\gamma_t\ge0$ for every $t$, and consider the run with any tie-break rule on any profile. For each $t=1,2,\dots,T+1$,
--
--   $$
--   \|p_t\|_\infty\le q+1.
--   $$
--
--   The bound on the price feeds the constant of Lemma 3, and at $t=T+1$ it bounds the overshoot.
--
--   Differences from the source:
--   - correction: Assumption 1 says nothing on f(0;θ); the proof treats x = 0 as having zero objective value → separate hypothesis f(0;θ) ≥ 0 for every θ; reason: Lemma 4 fails: Θ a point, 𝒳=[0,1], f(x)=min(4x−1,0), g(x)=x, q=0.01, c=T/8 satisfies Assumption 1, and at T=81 the price of IGD(γ̂) reaches 9/8 (Solutions/verification/OnlineWass_lemma4_instance.lean)
--   - generalization: Θ ⊂ ℝˡ → Θ any metric Borel space with distance (2); reason: ρ is the only structure the paper uses on Θ; a subset of ℝˡ with ρ is an instance
--   - generalization: x̃ₜ = argmax with no rule for ties → any jointly measurable tie-break rule sel; reason: every solver of line 4 that reads (pₜ, θₜ) is such a rule, and the bound holds for each
--   - generalization: t ≤ T, with probability 1, input γ̂ → t ≤ T + 1, every profile, any input γ ≥ 0; reason: (33) applies the lemma at T + 1 and the proof covers it; γ̂ₜ ≥ 0 is the only property used
--   - encoding: periods t = 1, …, T, p₁, p_{T+1} → t : Fin T is period t + 1; p₁ is index 0, p_{T+1} is index T; reason: Lean indices; same instances
-- source:
--   Jiang, Li & Zhang, Online Stochastic Optimization with Wasserstein Based Non-stationarity, arXiv:2012.06961v3, Lemma 4, p.22; proof p.55

import Mathlib
import Definitions.Def_OnlineWass_Model
import Definitions.Def_OnlineWass_igd

open MeasureTheory

namespace OnlineWass

/-- **Lemma 4, Jiang, Li & Zhang, arXiv:2012.06961v3, p.22 (proof p.55), corrected:** for any input
`γ ≥ 0`, on every profile and for `1 ≤ t ≤ T + 1`, `‖pₜ‖∞ ≤ q + 1`.

**Formalization Note.** Index `t` is `p_{t+1}` of the paper, so `t ≤ T` covers `p_{T+1}`, which (33) uses.
`γ̂ₜ ≥ 0` is the only property of the input that matters. -/
theorem lemma_4 {k m T : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    (M : Model k m Θ) (q : ℝ) (hA : Assumption1 M q)
    (hf0 : ∀ θ, 0 ≤ M.f 0 θ) (hT : 0 < T) (γ : Fin T → Fin m → ℝ) (hγ : ∀ t i, 0 ≤ γ t i)
    (sel : (Fin m → ℝ) → Θ → Fin k → ℝ) (hsel : IsTieBreak M sel)
    (H : Fin T → Θ) (t : ℕ) (ht : t ≤ T) :
    ‖price M sel γ H t‖ ≤ q + 1 := by sorry

end OnlineWass
