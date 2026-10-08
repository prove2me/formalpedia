-- Prove2me | Theorems.Thm_MinimaxRegretRL_Bernstein_variance_le_two_sum
-- name    : MinimaxRegretRL.Bernstein.variance_le_two_sum
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T16:08:15.26099+00:00
-- url     : https://prove2.me/theorems/3c3fbad0-59ed-4edc-8ee5-1d905184103c
-- title:
--   Lemma 2 — variance of a sum
-- statement:
--   Let $p$ be a probability distribution on a finite set, and let $X$ and $Y$ be real random variables on that set. Then
--
--   $$\operatorname{Var}_p(X)\le 2\bigl(\operatorname{Var}_p(Y)+\operatorname{Var}_p(X-Y)\bigr).$$
--
--   This compares the variance of a value estimate with that of a reference value and their difference in the Bernstein–Freedman analysis.
--
--   **Formalization Note** The finite setting makes both second moments finite automatically.
-- source:
--   Azar, Osband and Munos, Minimax Regret Bounds for Reinforcement Learning, arXiv:1703.05449v2 (2017), p. 19, Lemma 2

import Mathlib
import Definitions.Def_MinimaxRegretRL_Bernstein_FiniteVariance

namespace MinimaxRegretRL.Bernstein

/-- Lemma 2, p. 19. Any finite probability space is a valid setting for the two
real random variables; all its functions have finite second moment. -/
theorem variance_le_two_sum {Ω : Type*} [Fintype Ω] (p : Ω → ℝ)
    (hp : ∀ z, 0 ≤ p z) (hp1 : ∑ z, p z = 1) (X Y : Ω → ℝ) :
    finiteVar p X ≤ 2 * (finiteVar p Y + finiteVar p (fun z => X z - Y z)) := by sorry

end MinimaxRegretRL.Bernstein
