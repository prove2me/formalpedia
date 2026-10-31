-- Prove2me | Theorems.Thm_FoundationsRL_E2DStructured_ucb_certifies_dec_zero
-- name    : FoundationsRL.E2DStructured.ucb_certifies_dec_zero
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:26:34.737756+00:00
-- url     : https://prove2.me/theorems/24a933de-dbed-473a-a799-1e2cc9c69372
-- title:
--   Proposition 20 — the UCB strategy certifies $\mathrm{dec}_0(\mathcal F^t)\le\bar f^t(\pi^t)-\underline f^t(\pi^t)$
-- statement:
--   Let $\mathcal F^t$ be a class of reward functions whose values at each decision are bounded, with upper and lower confidence functions $\bar f^t$ and $\underline f^t$. Let $\pi^t\in\arg\max_{\pi\in\Pi}\bar f^t(\pi)$. Then the point mass at $\pi^t$ certifies
--   $$\mathrm{dec}_0(\mathcal F^t)\le\bar f^t(\pi^t)-\underline f^t(\pi^t),$$
--   that is, the inner value of the game at $\delta_{\pi^t}$ with $\gamma=0$ is at most the confidence width, for every reference model, and so is $\mathrm{dec}_0(\mathcal F^t)$.
--
--   This relates the DEC to the confidence width of the UCB analysis.
--
--   Differences from the source:
--   - generalization: F^t is a confidence set of E2D → G is any reward class with bounded pointwise values; reason: the proof uses nothing else; the confidence sets are a special case when their values are bounded
--   - encoding: max_{f∈F^t} and min_{f∈F^t} in f̄^t and f̲^t → real sSup and sInf, with pointwise values assumed bounded; reason: the printed max and min presuppose these bounds and the argmax of f̄^t is taken in the same sense
--   - encoding: f : Π → ℝ, π_f = arg max f; the single inequality (4.27) → every f ∈ G measurable with a maximizer; a conjunction of the certification by the point mass and (4.27); reason: the expectation is defined only then, and the word certifies on p. 69 is the first conjunct
--   - encoding: real expectations → Lebesgue integrals in [0, ∞], subtracted in EReal (the undefined case ∞ − ∞ scored −∞); reason: the integrand may be non-integrable for unbounded functions, where a Bochner integral would return 0
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, Proposition 20, (4.27), p. 76

import Mathlib
import Definitions.Def_FoundationsRL_E2DStructured_IsRewardClass
import Definitions.Def_FoundationsRL_E2DStructured_decHull
import Definitions.Def_FoundationsRL_E2DStructured_decGame
import Definitions.Def_FoundationsRL_E2DStructured_upperConf
import Definitions.Def_FoundationsRL_E2DStructured_lowerConf
import Definitions.Def_FoundationsRL_E2DStructured_pointMass

open MeasureTheory
open scoped ENNReal

namespace FoundationsRL.E2DStructured

/-- **Proposition 20** (Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*, arXiv:2312.16730v1, §4.4.1, p. 76, (4.27)): the UCB strategy `π^t = arg max_π f̄^t(π)`
certifies `dec_0(F^t) ≤ f̄^t(π^t) − f̲^t(π^t)`.

**Formalization Note.** `G` is `F^t`; the statement holds for every class, so nothing about the
construction of `F^t` is assumed. The first conjunct is the certification of p. 69 for the point mass
at `π^t`, against every reference model, as in the first line of the proof; the second is (4.27). -/
theorem ucb_certifies_dec_zero {D : Type*} [MeasurableSpace D] (G : Set (D → ℝ))
    (hG : IsRewardClass G)
    (hbddAbove : ∀ π, BddAbove ((fun f : D → ℝ => f π) '' G))
    (hbddBelow : ∀ π, BddBelow ((fun f : D → ℝ => f π) '' G))
    (πt : D) (hπt : ∀ π, upperConf G π ≤ upperConf G πt) :
    (∀ fhat : D → ℝ, decGame 0 G fhat (pointMass πt) ≤
        ((upperConf G πt - lowerConf G πt : ℝ) : EReal)) ∧
      decHull 0 G ≤ ((upperConf G πt - lowerConf G πt : ℝ) : EReal) := by sorry

end FoundationsRL.E2DStructured
