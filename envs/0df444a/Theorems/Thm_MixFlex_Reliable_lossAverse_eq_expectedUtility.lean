-- Prove2me | Theorems.Thm_MixFlex_Reliable_lossAverse_eq_expectedUtility
-- name    : MixFlex.Reliable.lossAverse_eq_expectedUtility
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T22:02:21.120814+00:00
-- url     : https://prove2.me/theorems/509dd47b-6cf8-4eb5-b4db-bf97b592be03
-- title:
--   Proof of Proposition 4(ii) — the loss-averse objective (6) is an expected utility with a nondecreasing piecewise-linear utility
-- statement:
--   Let $w_0\in\mathbb R$ be the initial wealth and $\beta\ge 1$ the loss-aversion coefficient, and define the piecewise-linear utility with breakpoint $w_0$,
--   $$
--   u_{LA}(w)=w_0+\max\{w-w_0,0\}-\beta\max\{-(w-w_0),0\}.
--   $$
--   Then
--   1. $u_{LA}$ is nondecreasing, so it belongs to the class $U_1$;
--   2. for every integrable terminal wealth $W$ on a probability space, the loss-averse objective (6) equals its expected utility:
--   $$
--   w_0+E\big[\tilde W^+-\beta\tilde W^-\big]=E\big[u_{LA}(W)\big],\qquad \tilde W=W-w_0 .
--   $$
--
--   With the expected-utility comparison this gives part (ii) of Proposition 4 for the loss-averse objective.
--
--   **Formalization Note** Integrability of $W$ is assumed so that $E[w_0+f(W)]=w_0+E[f(W)]$ holds for the Bochner integral (for non-integrable $W$ both sides default to junk values). The SD and SF wealths of the mission are almost surely bounded, so they satisfy it.
-- source:
--   Tomlin and Wang, On the value of mix flexibility and dual sourcing in unreliable newsvendor networks, Manufacturing Service Oper. Management 7(1), 2005, p. 53, Appendix A, proof of PROPOSITION 4(ii); p. 40, (6)

import Mathlib
import Definitions.Def_MixFlex_Reliable_Model

open MeasureTheory

namespace MixFlex.Reliable
theorem lossAverse_eq_expectedUtility (P : Params) (hP : P.Standing) {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] :
    Monotone (uLA P) ∧
      ∀ W : Ω → ℝ, Integrable W μ → lossAverseValue P μ W = expectedUtility μ (uLA P) W := by sorry
end MixFlex.Reliable
