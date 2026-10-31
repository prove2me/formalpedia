-- Prove2me | Theorems.Thm_FoundationsRL_E2DStructured_ucb_certifies_dec
-- name    : FoundationsRL.E2DStructured.ucb_certifies_dec
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:25:26.992093+00:00
-- url     : https://prove2.me/theorems/1fa5fad0-e89c-4711-9f51-5e09ee6cce01
-- title:
--   Proposition 21 — the UCB strategy certifies $\mathrm{dec}_\gamma(\mathcal F^t,\hat f^t)\le\bar f^t(\pi^t)-\hat f^t(\pi^t)+\frac1{4\gamma}$
-- statement:
--   Let $\mathcal F^t$ be a class of reward functions whose values at each decision are bounded above, with upper confidence function $\bar f^t$, and let $\hat f^t$ be a reference model. For any $\gamma>0$, if $\pi^t\in\arg\max_{\pi\in\Pi}\bar f^t(\pi)$, then the point mass at $\pi^t$ certifies
--   $$\mathrm{dec}_\gamma(\mathcal F^t,\hat f^t)\le\bar f^t(\pi^t)-\hat f^t(\pi^t)+\frac{1}{4\gamma}.$$
--
--   Compared with Proposition 20, allowing $\gamma>0$ replaces the lower confidence function by the estimate $\hat f^t$.
--
--   Differences from the source:
--   - generalization: F^t is a confidence set of E2D and f̂^t the estimate of round t → G is any reward class with values bounded above, fhat any measurable function; reason: the proof uses nothing else; the objects of the notes are a special case when the values are bounded
--   - encoding: max_{f∈F^t} in f̄^t → real sSup, with pointwise values assumed bounded above; reason: the printed max presupposes this bound
--   - encoding: f : Π → ℝ, π_f = arg max f; the single inequality → every f ∈ G measurable with a maximizer; a conjunction of the certification by the point mass and the inequality; reason: the expectation is defined only then, and the word certifies on p. 69 is the first conjunct
--   - encoding: real expectations → Lebesgue integrals in [0, ∞], subtracted in EReal (the undefined case ∞ − ∞ scored −∞); reason: the integrand may be non-integrable for unbounded functions, where a Bochner integral would return 0
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, Proposition 21, p. 77

import Mathlib
import Definitions.Def_FoundationsRL_E2DStructured_IsRewardClass
import Definitions.Def_FoundationsRL_E2DStructured_dec
import Definitions.Def_FoundationsRL_E2DStructured_upperConf
import Definitions.Def_FoundationsRL_E2DStructured_pointMass

open MeasureTheory
open scoped ENNReal

namespace FoundationsRL.E2DStructured

/-- **Proposition 21** (Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*, arXiv:2312.16730v1, §4.4.1, p. 77): for any `γ > 0`, the UCB strategy
`π^t = arg max_π f̄^t(π)` certifies `dec_γ(F^t, f̂^t) ≤ f̄^t(π^t) − f̂^t(π^t) + 1/(4γ)`.

**Formalization Note.** `G` is `F^t` and `fhat` is `f̂^t`; the statement holds for every class
and every measurable reference model. The first conjunct is the certification of p. 69 for the point
mass at `π^t`; the second is the printed inequality. -/
theorem ucb_certifies_dec {D : Type*} [MeasurableSpace D] (G : Set (D → ℝ))
    (hG : IsRewardClass G)
    (hbddAbove : ∀ π, BddAbove ((fun f : D → ℝ => f π) '' G))
    (γ : ℝ) (hγ : 0 < γ) (fhat : D → ℝ) (hfhat : Measurable fhat)
    (πt : D) (hπt : ∀ π, upperConf G π ≤ upperConf G πt) :
    decGame γ G fhat (pointMass πt) ≤ ((upperConf G πt - fhat πt + 1 / (4 * γ) : ℝ) : EReal) ∧
      dec γ G fhat ≤ ((upperConf G πt - fhat πt + 1 / (4 * γ) : ℝ) : EReal) := by sorry

end FoundationsRL.E2DStructured
