-- Prove2me | Theorems.Thm_FriedmannStochastic_absorption_values
-- name    : FriedmannStochastic.absorption_values
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-07T17:11:34.402084+00:00
-- url     : https://prove2.me/theorems/85e19095-adac-41d5-afe0-7a994928609b
-- title:
--   Absorption values for stopping stochastic games
-- statement:
--   For every well-formed stopping stochastic game and legal strategy pair, $I-P$ is nonsingular. Its absorption solution is one at the winning terminal, zero at the losing terminal, lies in $[0,1]$ everywhere, and satisfies the transition equations at every nonterminal state.
-- source:
--   Oliver Friedmann, An Exponential Lower Bound for the Latest Deterministic Strategy Iteration Algorithms, LMCS 2011, author PDF https://oliverfriedmann.com/downloads/papers/strategy_improvement_lower_bound_journal.pdf; arXiv:1106.0778v2 https://arxiv.org/abs/1106.0778; §9, almost-sure halting convention and Algorithm 4; equation-level infrastructure consequence

import Definitions.Def_friedmann_payoff

set_option autoImplicit false

namespace FriedmannStochastic

theorem absorption_values {V : Type} [Fintype V] [DecidableEq V]
    (G : Game V) (hG : WellFormed G) (σ τ : V → V)
    (hσ : Legal G 0 σ) (hτ : Legal G 1 τ) :
    (1 - transition G σ τ).det ≠ 0 ∧
    playValue G σ τ G.win = 1 ∧ playValue G σ τ G.lose = 0 ∧
    (∀ v, 0 ≤ playValue G σ τ v ∧ playValue G σ τ v ≤ 1) ∧
    (∀ v, v ≠ G.win → v ≠ G.lose →
      playValue G σ τ v = ∑ w, transition G σ τ v w * playValue G σ τ w) := by sorry

end FriedmannStochastic
