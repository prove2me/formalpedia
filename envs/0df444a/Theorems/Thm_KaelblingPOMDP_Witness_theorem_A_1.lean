-- Prove2me | Theorems.Thm_KaelblingPOMDP_Witness_theorem_A_1
-- name    : KaelblingPOMDP.Witness.theorem_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:13:17.280976+00:00
-- url     : https://prove2.me/theorems/1d1a6a04-03b8-4039-a21a-72be3d9ce2fb
-- title:
--   Theorem A.1 — the witness theorem: U_a ≠ Q^a_t iff a single-subtree replacement p_new beats every tree of U_a at some belief
-- statement:
--   Let $\langle S, A, T, R, \Omega, O\rangle$ be a POMDP with finite sets of states, actions and observations, stochastic transition and observation functions, and discount factor $0 < \gamma \le 1$. Fix $t \ge 2$ and an action $a$. Let $\mathcal V_{t-1}$ be the set of useful $(t-1)$-step policy trees, and let $\mathcal Q^a_t$ be the complete set of useful policy trees for $a$: the $t$-step trees with root $a$ and subtrees in $\mathcal V_{t-1}$ that are useful among all such trees.
--
--   **Theorem A.1.** Let $U_a \subseteq \mathcal Q^a_t$ be a nonempty set of useful policy trees. Then $U_a \ne \mathcal Q^a_t$ if and only if there are a tree $p \in U_a$, an observation $o^* \in \Omega$, a subtree $p' \in \mathcal V_{t-1}$ and a belief state $b$ such that
--   $$V_{p_{\mathrm{new}}}(b) > V_{\tilde p}(b) \quad \text{for all } \tilde p \in U_a, \tag{A.1}$$
--   where $p_{\mathrm{new}}$ is the $t$-step tree that agrees with $p$ in its action and all its subtrees except for observation $o^*$, for which $o^*(p_{\mathrm{new}}) = p'$.
--
--   Two trees are regarded as equal when they have the same value function. Theorem A.1 justifies the witness algorithm: to complete a partial set of useful trees it suffices to search over single-subtree modifications of the trees already found, a search that a linear program per modification carries out.
--
--   **Formalization Note** Since $U_a \subseteq \mathcal Q^a_t$ and trees are identified by value function, $U_a \ne \mathcal Q^a_t$ is stated as: some tree of $\mathcal Q^a_t$ has a value function different from that of every tree of $U_a$. Trees are indexed by depth minus one, so the theorem is stated for $t = n + 2$ with `PolicyTree A Ω (n + 1)`; `usefulTrees M n` is $\mathcal V_{t-1}$ and `Qset M a n` is $\mathcal Q^a_t$. Belief states range over `stdSimplex ℝ S`.
-- source:
--   Kaelbling, Littman, Cassandra, Planning and acting in partially observable stochastic domains, Artificial Intelligence 101:99–134 (1998), DOI 10.1016/S0004-3702(98)00023-X, p. 130, Theorem A.1

import Mathlib
import Definitions.Def_KaelblingPOMDP_Witness_Useful

namespace KaelblingPOMDP.Witness

open Finset

universe u

/-- **Theorem A.1** (Appendix A, p. 130, Kaelbling, Littman, Cassandra, *Planning and acting in partially observable stochastic domains*,
Artificial Intelligence 101:99–134 (1998)). Let `U_a` be a nonempty set of useful
policy trees, and `Q^a_t` be the complete set of useful policy trees. Then `U_a ≠ Q^a_t` if and only if
there is some tree `p ∈ U_a`, observation `o* ∈ Ω`, and subtree `p′ ∈ V_{t−1}` for which there is some
belief state `b` such that `V_{p_new}(b) > V_p̃(b)` for all `p̃ ∈ U_a`, where `p_new` agrees with `p` in
its action and all its subtrees except for observation `o*`, for which `o*(p_new) = p′`.

**Formalization Note**
* `t = n + 2` (a tree with subtrees has depth at least 2); `PolicyTree A Ω (n + 1)` is the type of
  t-step trees and `usefulTrees M n` is `V_{t−1}`, the useful (t − 1)-step trees among all of them.
* `Qset M a n` is `Q^a_t`: the trees useful within the candidate set (root `a`, every subtree in
  `V_{t−1}`).
* "Two trees are equal if they have the same value function" (p. 130). Since `U_a ⊆ Q^a_t`,
  `U_a ≠ Q^a_t` is stated as: some tree of `Q^a_t` has a value function different from that of every
  tree of `U_a`.
* Belief states range over `stdSimplex ℝ S`; `0 < γ ≤ 1` is part of `M.IsValid`. -/
theorem theorem_A_1 {S A Ω : Type u} [Fintype S] [DecidableEq S] [Nonempty S] [Fintype A] [DecidableEq A]
    [Nonempty A] [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
    (M : POMDP S A Ω) (hM : M.IsValid) (a : A) (n : ℕ)
    (U : Finset (PolicyTree A Ω (n + 1))) (hU : U.Nonempty) (hUQ : U ⊆ Qset M a n) :
    (∃ q ∈ Qset M a n, ∀ p ∈ U, value M p ≠ value M q) ↔
      ∃ p ∈ U, ∃ o : Ω, ∃ p' ∈ usefulTrees M n, ∃ b ∈ stdSimplex ℝ S,
        ∀ q ∈ U, valueAt M q b < valueAt M (p.replace o p') b := by sorry

end KaelblingPOMDP.Witness
