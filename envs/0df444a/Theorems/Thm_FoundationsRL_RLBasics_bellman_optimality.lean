-- Prove2me | Theorems.Thm_FoundationsRL_RLBasics_bellman_optimality
-- name    : FoundationsRL.RLBasics.bellman_optimality
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-18T05:02:18.573734+00:00
-- url     : https://prove2.me/theorems/9721a94c-9e0f-44ef-931b-5482e80c1908
-- title:
--   Proposition 25 — Bellman optimality
-- statement:
--   This is Proposition 25 (Bellman Optimality), the structural fact underlying every other result in the chapter.
--
--   Fix a finite-horizon episodic MDP $M$. Recall the optimal value functions $Q^{M,\star}_h(s,a) = \sup_{\pi\in\Pi^{\mathrm{rns}}} \mathbb E^{M,\pi}\big[\sum_{h'\ge h} r_{h'} \mid s_h=s,a_h=a\big]$ and $V^{M,\star}_h(s) = \max_a Q^{M,\star}_h(s,a)$ (Eq. (5.4)) — suprema over the whole (infinite) space of randomized non-stationary policies. The proposition asserts that there is a single **deterministic** policy $\pi_M$, greedy with respect to $Q^{M,\star}$ at every layer $h<H$ and state (i.e. $\pi_M(s) \in \arg\max_a Q^{M,\star}_h(s,a)$, Eq. (5.9)), such that:
--
--   1. $Q^{M,\star}$ satisfies the Bellman optimality recursion $Q^{M,\star}_h(s,a) = \big[T^M_h Q^{M,\star}_{h+1}\big](s,a)$ (Eqs. (5.8), (5.10)); and
--   2. $\pi_M$'s own value function equals $V^{M,\star}$ at **every** layer and **every** state simultaneously (Eq. (5.5)/(5.6)) — i.e. $\pi_M$ is optimal not just on average over the initial state distribution, but pointwise, for every starting state.
--
--   This existence of a single, simultaneously-optimal Markov policy is what lets dynamic programming replace an intractable search over $\Pi^{\mathrm{rns}}$ with $H$ one-step maximizations, and it underlies the correctness of value iteration.
--
--   **Formalization Note** Layers are $0$-indexed (`h` here is the book's `h+1`). `Qstar`/`Vstar` are defined as literal suprema over the policy type, not via a recursive shortcut, so this statement is not a restatement of a definition.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, p. 83–84, Prop. 25, Eqs. (5.5)–(5.9)

import Mathlib
import Definitions.Def_FoundationsRL_RLBasics_Core

namespace FoundationsRL.RLBasics

/-- **Proposition 25 (Bellman Optimality)** (Foster–Rakhlin, arXiv:2312.16730v1, p. 83,
Prop. 25, Eqs. (5.6)–(5.9)): there is a deterministic policy `πdet`, greedy at every layer
`h < H` w.r.t. `Qstar` (Eq. (5.9)), whose `Q`-values satisfy the Bellman optimality
recursion `Q^⋆_h(s,a) = [T^M_h Q^⋆_{h+1}](s,a)` (Eqs. (5.8), (5.10)) and whose value
function equals `Vstar` at every layer and state, i.e. `πdet` is simultaneously optimal
among all of `Π^{rns}` at every state (Eq. (5.5)). -/
theorem bellman_optimality {S A : Type*} [Fintype S] [Fintype A] [Nonempty A] [DecidableEq S]
    [DecidableEq A] {H : ℕ} (M : EpisodicMDP S A H) :
    ∃ πdet : ℕ → S → A,
      (∀ h, h < H → ∀ s : S, IsArgmax (Qstar M h s) (πdet h s)) ∧
      (∀ h, h < H → ∀ s : S, ∀ a : A, Qstar M h s a = bellmanOp M h (Qstar M (h + 1)) s a) ∧
      (∀ h, h ≤ H → ∀ s : S, V M (detPolicy πdet) h s = Vstar M h s) := by sorry

end FoundationsRL.RLBasics
