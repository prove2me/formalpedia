-- Prove2me | Theorems.Thm_MarkovEntanglementExact_Supplement_local_stationary_marginal
-- name    : MarkovEntanglementExact.Supplement.local_stationary_marginal
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T00:52:03.157908+00:00
-- url     : https://prove2.me/theorems/caf74886-e830-4c38-8773-4b416dedd4c1
-- title:
--   Lemma 5 — the agent marginal of a stationary occupancy is stationary for the local transition
-- statement:
--   Let $P$ be a transition matrix on $X_A\times X_B$ and $\mu$ a stationary distribution of $P$ ($\mu^\top P=\mu^\top$) whose agent marginals $\mu_A(x_A)=\sum_{x_B}\mu(x_A,x_B)$ and $\mu_B(x_B)=\sum_{x_A}\mu(x_A,x_B)$ are positive. Let $P^\pi_A$, $P^\pi_B$ be the local transitions of Eq. (2). Then
--   $$\mu_A^\top P^\pi_A=\mu_A^\top,\qquad \mu_B^\top P^\pi_B=\mu_B^\top,$$
--   i.e. the local stationary distribution of each agent is the marginal of the global one.
--
--   This identifies the weighting $\mu^\pi_i$ in Theorem 5: the weighted norm of each agent's local transition error is taken with respect to the agent marginal of the global stationary distribution.
--
--   Differences from the source:
--   - generalization: P^π_AB, the transition matrix of a two-agent MDP under π, with |S_A| = |S_B| and |A_A| = |A_B| → any transition matrix P on X_A × X_B for arbitrary finite types X_A, X_B of agent state-action pairs; reason: the proof uses only that P is a transition matrix; P^π_AB is an instance (published inducedMatrix_isTransitionMatrix), so the Lean statement specializes to the source
--   - generalization: Lemma 5 is printed for agent A ("the local stationary distribution of each agent") → both agents A and B; reason: the B case is the symmetric statement the sentence asserts; the A part is the printed lemma
--   - encoding: Eq. (2), the local transition as a conditional sum with µ(s_B, a_B | s_A, a_A) → IsLocalTransitionA/B, Eq. (2) multiplied by the positive marginal µ_A(s_A, a_A); reason: equivalent when the marginal is positive (footnote 1), which IsOccupancy assumes
-- source:
--   Chen & Peng, Multi-agent Markov Entanglement, arXiv:2506.02385v3, Lemma 5, p.38 (and §5.4, p.20)

import Mathlib
import Definitions.Def_markov_entanglement
import Definitions.Def_MarkovEntanglementExact_IsOccupancy

open scoped BigOperators
open MarkovEntanglement

namespace MarkovEntanglementExact.Supplement

/-- **Lemma 5** (the local stationary distribution is the marginal). Let `P` be a transition
matrix on the joint state-action pairs of two agents and `μ` a stationary distribution of `P`
with positive agent marginals. Then the local transition `P^π_A` of Eq. (2) has the marginal
`μ_A(s_A, a_A) = Σ_{s_B, a_B} μ(s_A, s_B, a_A, a_B)` as a stationary distribution, and likewise
`P^π_B` has `μ_B`.

Source: Chen & Peng, Multi-agent Markov Entanglement, arXiv:2506.02385v3, Lemma 5, p.38 ("the
local stationary distribution of each agent is exactly the marginal distribution of global
µ^π_AB"), and §5.4, p.20.

**Formalization Note.** `P` is any transition matrix on `XA × XB`; stationarity is the published
`IsStationary` (`μ P = μ`), and uniqueness is not assumed. -/
theorem local_stationary_marginal
    {XA XB : Type*} [Fintype XA] [Fintype XB] [DecidableEq XA] [DecidableEq XB]
    (P : Matrix (XA × XB) (XA × XB) ℝ) (hP : IsTransitionMatrix P)
    (μ : XA × XB → ℝ) (hμ : IsOccupancy μ) (hstat : IsStationary P μ)
    (PπA : Matrix XA XA ℝ) (PπB : Matrix XB XB ℝ)
    (hPπA : IsLocalTransitionA P μ PπA) (hPπB : IsLocalTransitionB P μ PπB) :
    IsStationary PπA (marginalA μ) ∧ IsStationary PπB (marginalB μ) := by sorry

end MarkovEntanglementExact.Supplement
