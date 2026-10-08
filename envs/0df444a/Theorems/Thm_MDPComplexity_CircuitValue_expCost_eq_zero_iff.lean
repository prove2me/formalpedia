-- Prove2me | Theorems.Thm_MDPComplexity_CircuitValue_expCost_eq_zero_iff
-- name    : MDPComplexity.CircuitValue.expCost_eq_zero_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:37:11.177353+00:00
-- url     : https://prove2.me/theorems/defc91a2-4810-40e2-9c22-2337b76c7ace
-- title:
--   Proof of Theorem 1 (p. 445): with nonnegative costs, zero expected cost iff no positive cost is incurred on a reachable trajectory
-- statement:
--   Let $M$ be a finite Markov decision process (states $S$, decisions $D_s$, costs $c(s,i,t)$, transition probabilities $p(s,s',i,t)$) whose costs are all nonnegative: $c(s,i,t)\ge0$. Fix an initial state $s_0$, a policy $\delta(s,t)$ and a horizon $T$. Then
--   $$
--   \mathbb E_\delta\Bigl[\sum_{t=0}^{T}c\bigl(s_t,\delta(s_t,t),t\bigr)\Bigr]=0
--   $$
--   if and only if, for every trajectory $x_0,\dots,x_T$ that has positive probability under $\delta$ from $s_0$, every cost incurred along it is zero: $c(x_t,\delta(x_t,t),t)=0$ for all $t=0,\dots,T$.
--
--   In the proof of Theorem 1 this is the step "there are decisions so that the states with positive costs are impossible to reach": a zero expected cost means that the policy never reaches, with positive probability, a state where it pays a positive cost.
--
--   **Formalization Note** Stated for an arbitrary finite, possibly nonstationary process with nonnegative costs, since the step does not use the circuit. "Impossible to reach" is read as "no trajectory of positive probability incurs a positive cost".
-- source:
--   Papadimitriou and Tsitsiklis, The Complexity of Markov Decision Processes, Math. Oper. Res. 12(3) (1987), p. 445, §3, proof of Theorem 1

import Mathlib
import Definitions.Def_MDPComplexity_CircuitValue_Model

namespace MDPComplexity.CircuitValue

open Finset BigOperators

theorem expCost_eq_zero_iff {S : Type} [Fintype S] [DecidableEq S] (M : MDP S)
    (hc : ∀ s i t, 0 ≤ M.c s i t) (s₀ : S) (δ : M.Policy) (T : ℕ) :
    M.expCost s₀ δ T = 0 ↔
      ∀ x : Fin (T + 1) → S, 0 < M.trajProb s₀ δ T x →
        ∀ t : Fin (T + 1), M.c (x t) (δ (x t) (t : ℕ)) (t : ℕ) = 0 := by sorry

end MDPComplexity.CircuitValue
