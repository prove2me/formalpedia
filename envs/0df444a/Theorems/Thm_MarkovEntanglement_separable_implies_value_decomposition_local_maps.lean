-- Prove2me | Theorems.Thm_MarkovEntanglement_separable_implies_value_decomposition_local_maps
-- name    : MarkovEntanglement.separable_implies_value_decomposition_local_maps
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-08-07T23:54:56.414701+00:00
-- url     : https://prove2.me/theorems/542194d2-a53e-448d-9aad-33bf52c27b9a
-- title:
--   Separability gives exact value decomposition by local maps of each agent's own reward
-- statement:
--   ## Statement
--
--   Let $P$ be a **separable** joint transition on the product state-action space of $N$ agents, and let $\gamma \in [0,1)$. Then there exist local value maps
--   $$Q_i \;:\; \mathbb{R}^{S_i} \longrightarrow \mathbb{R}^{S_i}, \qquad i = 1,\dots,N,$$
--   fixed once and for all, such that for **every** profile of local rewards $r_1,\dots,r_N$ the joint value function decomposes exactly:
--   $$Q^\pi_{1:N}(s,a) \;=\; \sum_{i=1}^{N} Q_i(r_i)\bigl(s_i,a_i\bigr) \qquad\text{for all } (s,a).$$
--
--   The point is the order of quantifiers: each $Q_i$ is chosen before any reward is seen, and reads **only agent $i$'s own reward**.
--
--   ## Notes
--
--   This is the faithful form of Theorem 1. A weaker reading — "for every reward profile, *some* additive decomposition of $Q$ exists" — puts the existential inside the universal and allows the witness for agent $i$ to depend on the entire reward profile. That weaker statement is strictly weaker: the paper's own Appendix E exhibits an entangled transition satisfying it. Since Theorem 2 is the converse of the strong form, only the strong form pairs with it to make Markov entanglement a *necessary and sufficient* condition for exact value decomposition.
--
--   **Why the local maps exist.** The proof does not go through a fixed-point iteration. Write $L = I - \gamma P$, so that the Bellman equation reads $LQ = R$. Two facts do all the work.
--
--   First, $L$ is injective: if $Lv = 0$ then $v = \gamma Pv$, and evaluating at a coordinate where $|v|$ is largest gives $|v| \le \gamma |v|$ with $\gamma < 1$.
--
--   Second — and this is what separability buys — for each agent $i$ the subspace
--   $$D_i \;=\; \bigl\{\, v \;:\; v(p) \text{ depends only on } p_i \,\bigr\}$$
--   is **separately** invariant under $P$, hence under $L$. Indeed if $P = \sum_k x_k \bigotimes_j P^{(k)}_j$ then
--   $$\sum_q P(p,q)\, g(q_i) \;=\; \sum_k x_k \sum_{t} P^{(k)}_i(p_i,t)\, g(t),$$
--   because the rows of every $P^{(k)}_j$ with $j \ne i$ sum to one and those coordinates integrate out.
--
--   So $L$ restricts to an injective, hence surjective, endomorphism of the finite-dimensional space $D_i$. Define $Q_i(r_i)$ to be the unique element of $D_i$ solving $L\,v = r_i(\cdot_i)$ — a definition that mentions $r_i$ alone. Summing over $i$ gives $L\bigl(\sum_i Q_i(r_i)\bigr) = R$, and injectivity of $L$ forces $Q = \sum_i Q_i(r_i)$.
--
--   The one-agent-at-a-time invariance is the crux: it is what makes the local maps canonical rather than merely existent. Note that no invertibility of $I - \gamma \sum_k x_k P^{(k)}_i$ on $\mathbb{R}^{S_i}$ is needed — and indeed none is available, since the coefficients $x_k$ of an affine combination may be negative and that matrix can be singular.
--
--   Search terms: value decomposition, separable transition kernel, multi-agent MDP, exact decomposition of Q function, local value functions, Bellman operator invariant subspace.
-- source:
--   Shuze Chen and Tianyi Peng, *Multi-agent Markov Entanglement*, arXiv:2506.02385v3, Theorem 1, p. 9

import Mathlib
import Definitions.Def_markov_entanglement_multi

open scoped BigOperators
open MarkovEntanglement

namespace MarkovEntanglement

theorem separable_implies_value_decomposition_local_maps
    {N : ℕ} {S : Fin N → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (P : Matrix (Joint S) (Joint S) ℝ) (hP : IsTransitionMatrix P) (hsep : IsSeparableN P)
    (γ : ℝ) (hγ : 0 ≤ γ) (hγ1 : γ < 1) :
    ∃ Qmap : ∀ i, (S i → ℝ) → (S i → ℝ),
      ∀ (r : ∀ i, S i → ℝ) (Q : Joint S → ℝ),
        IsBellmanQ P (fun p => ∑ i, r i (p i)) γ Q →
          ∀ p : Joint S, Q p = ∑ i, Qmap i (r i) (p i) := by
  sorry

end MarkovEntanglement
