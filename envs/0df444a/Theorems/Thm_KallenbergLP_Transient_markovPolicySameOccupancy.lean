-- Prove2me | Theorems.Thm_KallenbergLP_Transient_markovPolicySameOccupancy
-- name    : KallenbergLP.Transient.markovPolicySameOccupancy
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T10:19:25.195355+00:00
-- url     : https://prove2.me/theorems/1d7afc50-5f2c-4731-81f2-ffca4398150b
-- title:
--   Corollary 2.5.1 — a Markov policy with the same state-action probabilities
-- statement:
--   Consider a finite Markov decision model with state space $E$, admissible action sets $A(i)$ and substochastic transition numbers $p_{iaj}$. Let $C$ be the class of all policies (randomized and history dependent) and $C_M$ the class of memoryless (Markov) policies, whose decision at epoch $t$ depends only on $t$ and the current state.
--
--   Given any initial state $i\in E$ and any policy $R\in C$, there exists a policy $R_0\in C_M$ such that
--
--   $$P_{R_0}(X_t=j,\,Y_t=a\mid X_1=i)=P_R(X_t=j,\,Y_t=a\mid X_1=i)\qquad t\in\mathbb N,\ a\in A(j),\ j\in E.$$
--
--   This is the single-policy, single-initial-state case of Theorem 2.5.1 (Derman–Strauch). It is used in the proof of Lemma 3.2.2 to restrict a supremum over all policies to Markov policies.
--
--   **Formalization Note** The policy $R_0$ may depend on $i$. Lean's epoch index $t$ is the book's epoch $t+1$.
-- source:
--   Kallenberg, Linear Programming and Finite Markovian Control Problems, Mathematical Centre Tracts 148, Mathematisch Centrum, Amsterdam 1983, p. 33, Corollary 2.5.1

import Definitions.Def_KallenbergLP_Transient_Policy
set_option autoImplicit false

namespace KallenbergLP.Transient

/-- Corollary 2.5.1: for a fixed initial state, a memoryless policy reproduces every
state-action probability of an arbitrary policy. -/
theorem markovPolicySameOccupancy
    {N : ℕ} {α : Type} [Fintype α] [DecidableEq α]
    (M : MDP N α) (i : Fin N) (R : Policy M) :
    ∃ R₀ : Policy M, Memoryless M R₀ ∧
      ∀ (t : ℕ) (j : Fin N) (a : α), a ∈ M.actions j →
        occupancy M R₀ i j a t = occupancy M R i j a t := by sorry

end KallenbergLP.Transient
