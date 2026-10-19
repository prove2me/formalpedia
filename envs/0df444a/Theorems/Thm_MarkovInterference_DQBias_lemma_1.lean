-- Prove2me | Theorems.Thm_MarkovInterference_DQBias_lemma_1
-- name    : MarkovInterference.DQBias.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:18:57.980782+00:00
-- url     : https://prove2.me/theorems/7be78c57-4668-4cb3-b026-6a7690046bcb
-- title:
--   Lemma 1 — stationary-distribution perturbation identity
-- statement:
--   Let $P$ and $P'$ be primitive transition matrices on the same finite state space, with stationary distributions $\rho$ and $\rho'$. Write $(I-P)^\#$ for the group inverse defined using $\rho$. Then
--
--   $$\rho'^{\top}=\rho^{\top}+\rho'^{\top}(P'-P)(I-P)^\#.$$
--
--   This identity measures how a stationary law changes when the transition matrix changes; the paper iterates it to expand the average treatment effect.
--
--   **Formalization Note** Primitivity represents the paper's finite-state irreducible and aperiodic hypotheses. Both stationary vectors are probability distributions, as stated in the paper's Markov-chain setting.
-- source:
--   Farias, Li, Peng, Zheng, Markovian Interference in Experiments, arXiv:2206.02371v2, pp. 13–14, Lemma 1

import Mathlib
import Definitions.Def_MarkovInterference_DQBias_Chain

namespace MarkovInterference.DQBias

/-- Lemma 1, pp. 13–14: stationary-distribution perturbation. -/
theorem lemma_1 {S : Type} [Fintype S] [DecidableEq S]
    (P P' : Matrix S S ℝ) (rho rho' : S → ℝ)
    (hP : IsStochastic P) (hP' : IsStochastic P')
    (hp : IsPrimitive P) (hp' : IsPrimitive P')
    (hrho : IsStationaryDist P rho) (hrho' : IsStationaryDist P' rho') :
    rho' = rho + Matrix.vecMul rho' ((P' - P) * groupInv P rho) := by sorry

end MarkovInterference.DQBias
