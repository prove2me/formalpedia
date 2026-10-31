-- Prove2me | Theorems.Thm_FoundationsRL_OnlineLearning_remark_6_square_mixable
-- name    : FoundationsRL.OnlineLearning.remark_6_square_mixable
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:18:38.404813+00:00
-- url     : https://prove2.me/theorems/58d517dc-3123-4827-a2f4-8a2b4cb561ea
-- title:
--   Remark 6 — square loss is mixable with $\eta=2$, $c=1$ on $[0,1]$
-- statement:
--   Let $\mathcal Y=\mathcal Y'=[0,1]$ and let $\mathcal F$ be a finite class of functions into $[0,1]$. Then square loss is mixable with parameter $\eta=2$ and $c=1$: for any $x$ and any distribution $q\in\Delta(\mathcal F)$ there is a prediction $\hat f(x)\in[0,1]$ such that for all $y\in[0,1]$,
--   $$
--   (\hat f(x)-y)^2\le-\frac12\log\Big(\sum_{f\in\mathcal F}q(f)\exp\{-2(f(x)-y)^2\}\Big).
--   $$
--
--   This is the notes’ route to fast rates for square loss: with mixability, the log-loss potential argument goes through with an inequality in place of (1.27).
--
--   Differences from the source: none.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, Remark 6, (1.34), p. 18, and p. 19

import Mathlib
import Definitions.Def_FoundationsRL_OnlineLearning_Losses
import Definitions.Def_FoundationsRL_OnlineLearning_Mixable

namespace FoundationsRL.OnlineLearning

/-- **Remark 6 (square loss is mixable).** Foster & Rakhlin, Foundations of Reinforcement Learning and
Interactive Decision Making, arXiv:2312.16730v1, Remark 6, p. 19.

Square loss is mixable with parameter `η = 2` and `c = 1` when `Y = Y' = [0, 1]`: every finite class
of functions into `[0, 1]` satisfies (1.34) with these constants. -/
theorem remark_6_square_mixable {X : Type*} (F : Finset (X → ℝ))
    (hF : ∀ f ∈ F, ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) :
    IsMixableWith (Set.Icc (0 : ℝ) 1) (Set.Icc (0 : ℝ) 1) squareLoss F 2 1 := by sorry

end FoundationsRL.OnlineLearning
