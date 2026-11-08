-- Prove2me | Theorems.Thm_FriedmannParity_improvement_strict
-- name    : FriedmannParity.improvement_strict
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-07T17:10:44.486559+00:00
-- url     : https://prove2.me/theorems/8b89a83f-879f-4311-ac22-5cae2e46bdcb
-- title:
--   Strict improvement of game valuations
-- statement:
--   A legal strategy update in the improvement arena, containing a strict switch whenever the original strategy is improvable, weakly raises every vertex valuation and strictly raises the chosen successor valuation at some player-0 vertex.
-- source:
--   Oliver Friedmann, An Exponential Lower Bound for the Latest Deterministic Strategy Iteration Algorithms, LMCS 2011, author PDF https://oliverfriedmann.com/downloads/papers/strategy_improvement_lower_bound_journal.pdf; arXiv:1106.0778v2 https://arxiv.org/abs/1106.0778; §3, Theorem 3.2

import Definitions.Def_friedmann_parity

set_option autoImplicit false

namespace FriedmannParity

theorem improvement_strict {V : Type} [Fintype V] [DecidableEq V]
    (G : Game V) (hG : WellFormed G) (σ σ' : V → V)
    (hσ : Legal G false σ) (hi : Improvable G σ) (hs : Improvement G σ σ') :
    (∀ v, ValueLE G (value G σ v) (value G σ' v)) ∧
    ∃ v, G.owner v = false ∧ ValueLT G (value G σ (σ v)) (value G σ' (σ' v)) := by sorry

end FriedmannParity
