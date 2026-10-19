-- Prove2me | Theorems.Thm_NonstatRL_NoWidening_hitTime_le_inv_of_one_step_reach
-- name    : NonstatRL.NoWidening.hitTime_le_inv_of_one_step_reach
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T08:03:53.105988+00:00
-- url     : https://prove2.me/theorems/e7fb6ff4-5c3c-4868-99a7-9d726e80c802
-- title:
--   Proof of Proposition 4 — uniform one-step reachability bounds expected hitting time
-- statement:
--   Let $M$ be a finite MDP, fix a target state $s'$, and choose a deterministic stationary policy $f$. If every state has probability at least $\zeta>0$ of moving to $s'$ under its selected action, then for every starting state $s$,
--
--   $$\mathbb E[\Lambda(s'\mid f,s)]\le\frac1\zeta.$$
--
--   The hitting time counts the first transition into the target, including a return from $s'$ to itself. This is the quantitative step used to turn Lemma 13 into the diameter bound.
--
--   **Formalization Note** Expected hitting time is an extended nonnegative real, allowing infinity in the definition. The positive lower bound makes the asserted upper bound finite. The statement uses the paper's return-time convention, not the published `mdpTravelTime`.
-- source:
--   Cheung, Simchi-Levi & Zhu, Non-Stationary Reinforcement Learning: The Blessing of (More) Optimism, arXiv:1906.02922v4, p. 49, proof of Proposition 4, expected hitting-time claim

import Mathlib
import Definitions.Def_NonstatRL_Oracle_Model

open BanditAlgorithm

namespace NonstatRL.NoWidening

theorem hitTime_le_inv_of_one_step_reach {S A : ℕ}
    (Mw : FiniteMDP S A) (f : Fin S → Fin A) (s' : Fin S)
    (ζ : ℝ) (hζ : 0 < ζ)
    (hreach : ∀ x, ζ ≤ (Mw.P x (f x) s' : ℝ)) :
    ∀ s, NonstatRL.Oracle.hitTime Mw f s s' ≤ ENNReal.ofReal (1 / ζ) := by sorry

end NonstatRL.NoWidening
