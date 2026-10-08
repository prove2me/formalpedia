-- Prove2me | Theorems.Thm_KallenbergLP_Constrained_closedConvexHull_LD_eq_L
-- name    : KallenbergLP.Constrained.closedConvexHull_LD_eq_L
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:11:58.181805+00:00
-- url     : https://prove2.me/theorems/da9818ce-eb9a-4bb0-8875-ccb0e607de2f
-- title:
--   Theorem 4.7.1 — the closed convex hulls of L(D) and L(S) equal L(C) = L(M) = L
-- statement:
--   Let $\beta$ be an initial distribution ($\beta_j\ge0$, $\sum_j\beta_j=1$; zeros allowed) for a finite Markov decision model with stochastic transitions. For a class of policies $C'$ let $L(C')$ be the set of all limit points of the expected state-action frequency vectors $x^T(R)$ of policies $R\in C'$; write $L$, $L(M)$, $L(C)$, $L(S)$, $L(D)$ for the classes of all, Markov, single-limit-point ($C_1$), stationary and pure stationary policies. Then
--
--   $$\overline{L(D)}=\overline{L(S)}=L(C)=L(M)=L,$$
--
--   where the bar denotes the closed convex hull.
--
--   The theorem says that, for any criterion that depends only on limit points of the expected state-action frequencies, it suffices to consider Markov policies, or policies with a single limit point, and that every achievable limit point is a mixture of the finitely many frequency vectors of pure stationary policies.
--
--   **Formalization Note** The bar is Mathlib's `closedConvexHull ℝ`.
-- source:
--   Kallenberg, Linear Programming and Finite Markovian Control Problems, Mathematical Centre Tracts 148, Mathematisch Centrum, Amsterdam 1983, p. 135, Theorem 4.7.1

import Mathlib
import Definitions.Def_MarkovDecisionProcesses_AverageReward
import Definitions.Def_KallenbergLP_Constrained_Frequencies

namespace KallenbergLP.Constrained

open MarkovDecisionProcesses

/-- Kallenberg (1983), Theorem 4.7.1, p. 135: `L̄(D) = L̄(S) = L(C) = L(M) = L`, where the bar is
the closed convex hull (Definition 1.2.1(i), p. 9). -/
theorem closedConvexHull_LD_eq_L {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S]
    [DecidableEq A] (M : StationaryMDP S A) (β : S → ℝ) (hβ0 : ∀ j, 0 ≤ β j)
    (hβ1 : ∑ j, β j = 1) :
    closedConvexHull ℝ (Lset M β IsPureStationary) = closedConvexHull ℝ (Lset M β IsStationary) ∧
    closedConvexHull ℝ (Lset M β IsStationary) = Lset M β (IsC1 β) ∧
    Lset M β (IsC1 β) = Lset M β IsMarkov ∧
    Lset M β IsMarkov = Lset M β (fun _ => True) := by sorry

end KallenbergLP.Constrained
