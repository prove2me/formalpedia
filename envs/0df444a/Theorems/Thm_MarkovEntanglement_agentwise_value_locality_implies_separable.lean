-- Prove2me | Theorems.Thm_MarkovEntanglement_agentwise_value_locality_implies_separable
-- name    : MarkovEntanglement.agentwise_value_locality_implies_separable
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-07T19:32:22.240786+00:00
-- url     : https://prove2.me/theorems/8ad6825f-9aa7-4ebb-bb31-ee9d894ee63f
-- title:
--   Higher-order reward necessity: order-$(N-1)$ value locality forces separability
-- statement:
--   ## Setup and notation
--
--   Fix an $N$-agent MDP $\mathcal{M}_{1:N}$ and a policy $\pi$. Agent $i$ has finite local state-action space $S_i$, the joint space is $S_{1:N}=S_1\times\cdots\times S_N$, and the policy induces the joint transition matrix $P^{\pi}_{1:N}$. Fix a discount factor $\gamma\in(0,1)$, so that $I-\gamma P^{\pi}_{1:N}$ is invertible and the $Q$-function of a joint reward $r$ is
--   $$Q^{\pi}_{1:N}\;=\;\bigl(I-\gamma P^{\pi}_{1:N}\bigr)^{-1}r .$$
--
--   Write $e$ for the all-ones vector, and for $i\in[N]$ let $r_{-i}$ denote a function of the $N-1$ agents other than $i$, i.e. an element of $\bigotimes_{j\neq i}\mathbb{R}^{S_j}$. We write
--   $$e_i\otimes r_{-i}$$
--   for the joint reward which places $e$ in agent $i$'s tensor slot and $r_{-i}$ on the remaining slots — that is, the reward that ignores agent $i$ but may couple the other $N-1$ agents arbitrarily. Rewards of this form are the **order-$(N-1)$** rewards; the **order-$1$** rewards $\sum_{i}e_{-i}\otimes r_i$ used in Theorem 1 and Theorem 2 are the special case in which each $r_{-i}$ itself factors as a single local reward tensored with $e$'s.
--
--   Recall Definition 10: $P^{\pi}_{1:N}$ is **separable** if
--   $$P^{\pi}_{1:N}\;=\;\sum_k x_k\,P^k_1\otimes\cdots\otimes P^k_N,\qquad \sum_k x_k=1,$$
--   with each $P^k_i$ a transition matrix on $S_i$, and **entangled** otherwise.
--
--   ## Statement
--
--   **Theorem (Higher-order reward necessity).** *Let $P^{\pi}_{1:N}$ be an $N$-agent transition matrix and $0<\gamma<1$. Suppose that for every $i\in[N]$ and every reward $r_{-i}$ depending arbitrarily on all agents except agent $i$, there exists a function $Q_{-i}$ depending only on those same $N-1$ agents such that*
--   $$\bigl(I-\gamma P^{\pi}_{1:N}\bigr)^{-1}\bigl(e_i\otimes r_{-i}\bigr)\;=\;e_i\otimes Q_{-i}.$$
--   *Then $P^{\pi}_{1:N}$ is separable.*
--
--   Equivalently, in the fixed-point form used in the formalisation: for each $i$, whenever a reward $r$ satisfies $r(p[i\mapsto t])=r(p)$ for all joint pairs $p$ and all $t\in S_i$ — where $p[i\mapsto t]$ is $p$ with its $i$-th coordinate overwritten by $t$ — every solution $Q$ of the Bellman equation $Q=r+\gamma P^{\pi}_{1:N}Q$ satisfies $Q(p[i\mapsto t])=Q(p)$ as well. The two formulations agree because $\gamma<1$ makes the Bellman solution unique and equal to $(I-\gamma P^{\pi}_{1:N})^{-1}r$.
--
--   ## Why order $N-1$
--
--   Let $\Omega$ denote the span of the local transition matrices, which by Lemma 3 (p. 34) is the space of matrices whose rows all sum to a common value, so that the separable matrices span $\Omega^{\otimes N}$. Writing $A=(I-\gamma P^{\pi}_{1:N})^{-1}$, the hypothesis for agent $i$ says exactly that $A$ carries $e_i\otimes(\,\cdot\,)$ into $e_i\otimes(\,\cdot\,)$, which is a constraint on the $i$-th tensor factor alone:
--   $$A\;\in\;\mathbb{R}^{S_1\times S_1}\otimes\cdots\otimes\Omega_i\otimes\cdots\otimes\mathbb{R}^{S_N\times S_N}.$$
--   Imposing this for every $i$ gives
--   $$A\;\in\;\bigcap_{i=1}^{N}\Bigl(\mathbb{R}^{S_1\times S_1}\otimes\cdots\otimes\Omega_i\otimes\cdots\otimes\mathbb{R}^{S_N\times S_N}\Bigr)\;=\;\Omega_1\otimes\cdots\otimes\Omega_N .$$
--   Since $(1-\gamma)A$ is itself a transition matrix, it is an affine combination of tensor products of local transition matrices, and Lemma 4 (p. 35) transfers separability from the resolvent back to $P^{\pi}_{1:N}$. In entries, the hypothesis for agent $i$ reads: the partial row sum $\sum_{t\in S_i}A(p,\,q[i\mapsto t])$ does not depend on $p_i$.
--
--   Order $N-1$ cannot be lowered. For each $k\le N-2$ the perturbation
--   $$T\;=\;(\varepsilon e^\top)\otimes(e\varepsilon^\top)^{\otimes(k+1)}\otimes(ee^\top)^{\otimes(N-k-2)},\qquad \varepsilon=(1,-1)^\top,$$
--   added to $U^{\otimes N}$ with $U=\tfrac12 ee^\top$ produces an entangled transition matrix that is invisible to every reward supported on at most $k$ agents, because $\varepsilon^\top e=0$ annihilates each such reward in one of the slots ending in $\varepsilon^\top$. At $k=1$ and $N=3$ this is the counterexample showing that the order-$1$ hypothesis of Theorem 2 does not suffice beyond two agents.
--
--   ## Relation to Theorem 2
--
--   For $N=2$ an order-$(N-1)=$ order-$1$ reward is just a single local reward, so the hypothesis becomes: every reward depending only on agent $B$ has a value depending only on agent $B$, and symmetrically. That is the hypothesis of Theorem 2 (p. 12), which the source states for two agents; the theorem above is its correct extension to arbitrary $N$, obtained by raising the order of the admissible rewards from $1$ to $N-1$ rather than by changing the conclusion.
--
--   The converse is elementary: if $P^{\pi}_{1:N}$ is separable then so is $A$, and a tensor product of matrices drawn from $\Omega$ maps $e_i\otimes r_{-i}$ to $e_i\otimes Q_{-i}$. Together with Theorem 1 (p. 9), higher-order reward necessity makes agent-wise value locality an exact characterisation of separability for any number of agents.
-- source:
--   Chen and Peng, Multi-agent Markov Entanglement, arXiv:2506.02385v3, Theorem 2 p. 12 (stated for two agents), Lemma 3 p. 34, Lemma 4 p. 35

import Mathlib
import Definitions.Def_markov_entanglement_multi

open scoped BigOperators
open MarkovEntanglement

namespace MarkovEntanglement

theorem agentwise_value_locality_implies_separable
    {N : ℕ} {S : Fin N → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (P : Matrix (Joint S) (Joint S) ℝ) (hP : IsTransitionMatrix P)
    (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ < 1)
    (hloc : ∀ (i : Fin N) (r Q : Joint S → ℝ),
      (∀ p q : Joint S, (∀ j, j ≠ i → p j = q j) → r p = r q) →
      IsBellmanQ P r γ Q →
      ∀ p q : Joint S, (∀ j, j ≠ i → p j = q j) → Q p = Q q) :
    IsSeparableN P := by
  sorry

end MarkovEntanglement
