-- Prove2me | Theorems.Thm_FriedmannDiscounted_discounted_bellman
-- name    : FriedmannDiscounted.discounted_bellman
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-07T17:11:21.332261+00:00
-- url     : https://prove2.me/theorems/1c291312-5b73-4b57-9000-bb6c7ba68555
-- title:
--   Unique discounted Bellman solution
-- statement:
--   For any finite total rational-reward game, any rational discount strictly between zero and one, and any pair of successor functions, the matrix-defined payoff vector satisfies the fixed-strategy discounted Bellman equations, and every rational solution equals that vector. Legality of the functions is unnecessary for this equation-level statement.
-- source:
--   Oliver Friedmann, An Exponential Lower Bound for the Latest Deterministic Strategy Iteration Algorithms, LMCS 2011, author PDF https://oliverfriedmann.com/downloads/papers/strategy_improvement_lower_bound_journal.pdf; arXiv:1106.0778v2 https://arxiv.org/abs/1106.0778; §9, discounted payoff definition and Algorithm 2; equation-level infrastructure consequence

import Definitions.Def_friedmann_payoff

set_option autoImplicit false

namespace FriedmannDiscounted

theorem discounted_bellman {V : Type} [Fintype V] [DecidableEq V]
    (G : Game V) (hG : WellFormed G) (σ τ : V → V) :
    (∀ v, playValue G σ τ v = G.reward v + G.discount *
      playValue G σ τ (if G.arena.owner v = false then σ v else τ v)) ∧
    ∀ x : V → ℚ,
      (∀ v, x v = G.reward v + G.discount *
        x (if G.arena.owner v = false then σ v else τ v)) → x = playValue G σ τ := by sorry

end FriedmannDiscounted
