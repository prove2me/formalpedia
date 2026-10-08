-- Prove2me | Theorems.Thm_KallenbergLP_Bias_abel_bound
-- name    : KallenbergLP.Bias.abel_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T11:04:31.585594+00:00
-- url     : https://prove2.me/theorems/758ee730-a571-45cb-ac46-b77b16153a7a
-- title:
--   Lemma 5.2.1 — upper average reward bounds the Abel limsup
-- statement:
--   For any policy $R$ and initial state $i$ in the finite stochastic Markov decision model, its upper average reward is at least the Abel limsup of its discounted rewards:
--
--   $$
--   \hat\phi_i(R)\ge\limsup_{\beta\uparrow1}(1-\beta)v_i^\beta(R).
--   $$
--
--   The lemma links the upper Cesàro average for a general history-dependent policy to its discounted performance as the discount factor approaches one.
-- source:
--   Kallenberg, Linear Programming and Finite Markovian Control Problems, Mathematical Centre Tracts 148, Mathematisch Centrum, Amsterdam 1983, p. 162, Lemma 5.2.1; https://ir.cwi.nl/pub/13008

import Definitions.Def_KallenbergLP_Bias_Criteria

open Filter

namespace KallenbergLP.Bias

/-- Lemma 5.2.1 (p. 162): upper average reward bounds the Abel limsup. -/
theorem abel_bound {N : ℕ} {α : Type} [Fintype α] [DecidableEq α]
    (M : MDP N α) (R : Policy M) (i : Fin N) :
    limsup (fun β : ℝ => (1 - β) * discountedReward M R i β)
      (nhdsWithin 1 (Set.Iio 1)) ≤ upperAverageReward M R i := by sorry

end KallenbergLP.Bias
