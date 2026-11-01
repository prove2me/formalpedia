-- Prove2me | Theorems.Thm_OnlineWass_exists_tieBreak
-- name    : OnlineWass.exists_tieBreak
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:17:31.903834+00:00
-- url     : https://prove2.me/theorems/8ddd516c-9378-4a7c-b898-c5bfa59babb8
-- title:
--   Algorithm 1 line 4 — a measurable tie-break rule exists
-- statement:
--   Under the model's hypotheses (compact $\mathcal X$, continuity, Assumption 1 (a), (b), and $\rho$ of (2) as the distance of $\Theta$) there is a jointly measurable map $\mathrm{sel}$ such that for all $p\ge0$ and $\theta\in\Theta$, $\mathrm{sel}(p,\theta)\in\mathcal X$ maximizes
--
--   $$
--   x\mapsto f(x;\theta)-p^\top g(x;\theta)
--   $$
--
--   over $\mathcal X$.
--
--   Such a rule is what turns step 4 of Algorithm 1 into a policy with measurable outputs.
--
--   Differences from the source:
--   - generalization: Θ ⊂ ℝˡ → Θ any metric Borel space with distance (2); reason: ρ is the only structure the paper uses on Θ; a subset of ℝˡ with ρ is an instance
--   - encoding: "solve x̃ₜ = argmax" → existence of a measurable selection; reason: line 4 gives no measurability; the paper needs one for its expectations
-- source:
--   Jiang, Li & Zhang, Online Stochastic Optimization with Wasserstein Based Non-stationarity, arXiv:2012.06961v3, Algorithm 1 line 4, p.17

import Mathlib
import Definitions.Def_OnlineWass_Model
import Definitions.Def_OnlineWass_igd

open MeasureTheory

namespace OnlineWass

/-- **Algorithm 1 line 4, Jiang, Li & Zhang, arXiv:2012.06961v3, p.17: a tie-break rule exists.**
There is a jointly measurable `sel` with `sel p θ` a maximizer of `f(x; θ) − pᵀg(x; θ)` over `𝒳` for all
`p ≥ 0` and `θ`. -/
theorem exists_tieBreak {k m : ℕ} {Θ : Type*} [MetricSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    (M : Model k m Θ) (hA : Assumption1ab M) (hρ : DistEqRho M) :
    ∃ sel, IsTieBreak M sel := by sorry

end OnlineWass
