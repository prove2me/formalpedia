-- Prove2me | Theorems.Thm_MDPFinance_Stationary_reward_iteration_stationary
-- name    : MDPFinance.Stationary.reward_iteration_stationary
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T21:46:20.652571+00:00
-- url     : https://prove2.me/theorems/763a8db8-d277-4731-a096-5837cb0431e1
-- title:
--   Theorem 2.5.3 — Reward Iteration
-- statement:
--   For a policy sequence $\pi = (f_0,\dots,f_{n-1})$ of a stationary Markov Decision Model,
--   $J_n^\pi = T^{f_0} T^{f_1} \cdots T^{f_{n-1}} g$ (operator composition, outermost $f_0$ first).
--
--   **Formalization Note.** $J_n^\pi$ (`Jpi`) is the independent, expectation-based definition;
--   this theorem equates it with the operator-composition helper `TfComposeChain`, so the
--   equality is genuine content, not a restatement of either side's own definition.
--
--   **Formalization Note (moderation).** The Integrability Assumption (AN) of Section 2.5, the
--   book's standing assumption, is carried as the explicit hypothesis `hAN`.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 41, PDF 56, Theorem 2.5.3

import Mathlib
import Definitions.Def_MDPFinance_Stationary_Model
import Definitions.Def_MDPFinance_Stationary_Policy
import Definitions.Def_MDPFinance_Stationary_Operators
import Definitions.Def_MDPFinance_Stationary_ValueFunction

open MeasureTheory ProbabilityTheory

namespace MDPFinance.Stationary

/-- Theorem 2.5.3 (Reward Iteration) (Bäuerle–Rieder, p. 41, PDF 56), under the standing
Integrability Assumption (AN) for the `N`-stage model, `n ≤ N`. For `π = (f_0, …,
f_{n-1})` it holds: `J_n^π = T^{f_0} … T^{f_{n-1}} g`. -/
theorem reward_iteration_stationary {E A : Type*} [MeasurableSpace E] [MeasurableSpace A]
    (M : StationaryMarkovDecisionModel E A) (N : ℕ) (hAN : IntegrabilityAssumption M N)
    (π : ℕ → E → A) (n : ℕ) (hn : n ≤ N) (hπ : IsPolicySeq M n π) :
    Jpi M π n = TfComposeChain M π n (fun x => (M.g x : EReal)) := by sorry

end MDPFinance.Stationary
