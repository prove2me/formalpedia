-- Prove2me | Theorems.Thm_MulticlassQNet_SingleStation_proof_8_4_projection_subset
-- name    : MulticlassQNet.SingleStation.proof_8_4_projection_subset
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T08:13:04.917292+00:00
-- url     : https://prove2.me/theorems/997f2f1b-582e-44f1-83f6-90ac508ee1ea
-- title:
--   Proof of Theorem 8.4 — the projection of P2 onto the n_i coordinates lies in P1
-- statement:
--   Consider the multiclass single-server queue with classes $E=\{1,\dots,n\}$, arrival rates $\lambda_i>0$, service rates $\mu_i>0$ and load $\sum_{i\in E}\lambda_i/\mu_i<1$, and the polyhedra P1 (Theorem 8.3) and P2 (Theorem 8.4). Let
--   $$
--   \mathrm{P2}'=\{(n_i)_{i\in E}:\ \exists\,(I_{ij})_{i,j\in E}\ \text{with}\ ((n_i),(I_{ij}))\in\mathrm{P2}\}
--   $$
--   be the projection of P2 onto the $n_i$ coordinates. Then
--   $$
--   \mathrm{P2}'\subseteq\mathrm{P1}.
--   $$
--   In words: whenever nonnegative $n_i$, $I_{ij}$ satisfy $\mu_iI_{ii}-\lambda_in_i=\lambda_i$, $\mu_iI_{ij}+\mu_jI_{ji}-\lambda_jn_i-\lambda_in_j=0$ ($i\neq j$) and $\sum_iI_{ij}=n_j$, the vector $(n_i)$ satisfies every inequality (64) and the equality (65).
--
--   This is the easy half of Theorem 8.4; the paper obtains it from Theorem 4.4 (the nonparametric polyhedron is at least as tight as the first-order bounds), specialized to one station with work conservation.
--
--   **Formalization Note** The projection is written $\{x \mid \exists I,\ (x,I)\in\mathrm{P2}\}$. Conventions are those of the definition `MulticlassQNet.SingleStation.Polyhedra`.
-- source:
--   Bertsimas, Paschalidis, Tsitsiklis, Optimization of Multiclass Queueing Networks: Polyhedral and Nonlinear Characterizations of Achievable Performance, MIT Sloan WP #3509-92-MSA (Dec. 1992), p. 38, §8.2, proof of Theorem 8.4 (using Theorem 4.4, p. 21)

import Mathlib
import Definitions.Def_MulticlassQNet_SingleStation_Polyhedra

namespace MulticlassQNet.SingleStation

/-- Proof of Theorem 8.4 (p. 38), first half ("In Theorem 4.4 we have shown that P2' ⊆ P1"):
the projection of P2 on the `n_i` coordinates is contained in P1. -/
theorem proof_8_4_projection_subset {n : ℕ} (lam mu : Fin n → ℝ)
    (hlam : ∀ i, 0 < lam i) (hmu : ∀ i, 0 < mu i) (hload : ∑ i, lam i / mu i < 1) :
    {x : Fin n → ℝ | ∃ I, (x, I) ∈ P2 lam mu} ⊆ P1 lam mu := by sorry

end MulticlassQNet.SingleStation
