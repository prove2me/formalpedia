-- Prove2me | Theorems.Thm_KallenbergLP_AverageLP_theorem_4_2_3
-- name    : KallenbergLP.AverageLP.theorem_4_2_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T10:33:44.66711+00:00
-- url     : https://prove2.me/theorems/3d12f5c6-d3e2-4e48-bd4d-4153ae5805a4
-- title:
--   Theorem 4.2.3 — a pure stationary average optimal policy also maximises the lim sup average reward
-- statement:
--   In a finite Markov decision model with stochastic transition rows, let
--   $$\hat\phi_i(R):=\limsup_{T\to\infty}\frac1T\sum_{t=1}^T\sum_j\sum_a\mathbb P_R(X_t=j,\ Y_t=a\mid X_1=i)\,r_{ja},\qquad i\in E,$$
--   be the lim sup average reward (4.2.9). If $f^\infty$ is a pure and stationary policy that is average optimal (for the lim inf criterion, $\phi(f^\infty)=\sup_R\phi(R)$), then
--   $$\hat\phi(f^\infty)\ge\hat\phi(R)\qquad\text{for every policy }R,$$
--   componentwise. So a pure stationary average optimal policy stays optimal under the stronger, lim sup, criterion.
-- source:
--   Kallenberg, Linear Programming and Finite Markovian Control Problems, Mathematical Centre Tracts 148, Mathematisch Centrum, Amsterdam 1983, p. 101, Theorem 4.2.3

import Mathlib
import Definitions.Def_MarkovDecisionProcesses_AverageReward
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
import Definitions.Def_KallenbergLP_AverageLP_Model
open MarkovDecisionProcesses BlackwellDiscreteDP.NearOne Matrix Filter

namespace KallenbergLP.AverageLP

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]

/-- **Theorem 4.2.3.** Let `f^∞` be any pure and stationary average optimal policy. Then
`φ̂(f^∞) ≥ φ̂(R)` for all `R ∈ C`, where `φ̂` is the lim sup average reward (4.2.9).

Kallenberg, Linear Programming and Finite Markovian Control Problems, Mathematical Centre Tracts 148, Mathematisch Centrum, Amsterdam 1983, p. 101, Theorem 4.2.3.

**Formalization Note.** Average optimality is the book's lim inf notion (`IsAvgOptimal`); `R`
ranges over all history-dependent randomized policies. -/
theorem theorem_4_2_3 (M : StationaryMDP S A) (f : S → A) (hf : ∀ i, f i ∈ M.admissible i)
    (hopt : IsAvgOptimal M (stationaryPolicy M f hf)) :
    ∀ (R : AvgHRPolicy M) (i : S), gainSup R i ≤ gainSup (stationaryPolicy M f hf) i := by sorry

end KallenbergLP.AverageLP
