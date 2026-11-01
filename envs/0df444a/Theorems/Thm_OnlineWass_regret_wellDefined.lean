-- Prove2me | Theorems.Thm_OnlineWass_regret_wellDefined
-- name    : OnlineWass.regret_wellDefined
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:17:45.448372+00:00
-- url     : https://prove2.me/theorems/98ef23cd-9f70-4db4-ad99-951c7418f8c2
-- title:
--   (3) — the regret is well defined
-- statement:
--   Let $\mathbb P=\mathcal P_1\otimes\dots\otimes\mathcal P_T$ be a product of probability measures on $\Theta$, $c\ge0$, $\gamma$ any input and $\mathrm{sel}$ a tie-break rule. Under the model's hypotheses, the four functions of $\mathcal H\in\Theta^T$
--
--   $$
--   R^*_T,\qquad R_T(\pi),\qquad \sum_{t=1}^T f(\tilde x_t;\theta_t),\qquad \sum_{i=1}^m\Bigl[\sum_{t=1}^T g_i(\tilde x_t;\theta_t)-(c_i-1)\Bigr]^+
--   $$
--
--   are integrable under $\mathbb P$.
--
--   So the expectations in the regret (3), and in every step of its analysis, are genuine. In particular the offline value is measurable, which the paper uses tacitly.
--
--   Differences from the source:
--   - generalization: Θ ⊂ ℝˡ → Θ any metric Borel space with distance (2); reason: ρ is the only structure the paper uses on Θ; a subset of ℝˡ with ρ is an instance
--   - generalization: regret of IGD(γ̂) → any input γ, and two extra integrands; reason: covers the plan's γ̂ and the terms of the proof on p.56
--   - encoding: EH∼P [RegT(H, π)] written as if finite → integrability as a statement; reason: Bochner integrals are 0 on non-integrable functions, so the fact must be stated
-- source:
--   Jiang, Li & Zhang, Online Stochastic Optimization with Wasserstein Based Non-stationarity, arXiv:2012.06961v3, (3), p.11

import Mathlib
import Definitions.Def_OnlineWass_Model
import Definitions.Def_OnlineWass_igd
import Definitions.Def_OnlineWass_benchmarks

open MeasureTheory

namespace OnlineWass

/-- **Regret (3) of Jiang, Li & Zhang, arXiv:2012.06961v3, p.11, is well defined.** Under the product law
`ℙ = ⊗ₜ𝒫ₜ`, the offline value `R*_T`, the reward `R_T(π)` of the run of IGD(γ) for any input `γ`, the
virtual reward and the overshoot are integrable.

**Formalization Note.** Every Bochner integral of `H` in this mission is of one of these four. -/
theorem regret_wellDefined {k m T : ℕ} {Θ : Type*} [MetricSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    (M : Model k m Θ) (hA : Assumption1ab M) (hρ : DistEqRho M) (hT : 0 < T)
    (c : Fin m → ℝ) (hc : 0 ≤ c) (γ : Fin T → Fin m → ℝ)
    (sel : (Fin m → ℝ) → Θ → Fin k → ℝ) (hsel : IsTieBreak M sel)
    (P : Fin T → Measure Θ) [∀ t, IsProbabilityMeasure (P t)] :
    Integrable (fun H => offlineValue M c H) (Measure.pi P) ∧
      Integrable (fun H => onlineReward M sel γ c H) (Measure.pi P) ∧
      Integrable (fun H => virtualReward M sel γ H) (Measure.pi P) ∧
      Integrable (fun H => overshoot M sel γ c H) (Measure.pi P) := by sorry

end OnlineWass
