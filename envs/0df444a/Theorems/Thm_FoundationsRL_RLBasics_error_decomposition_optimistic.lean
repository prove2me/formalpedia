-- Prove2me | Theorems.Thm_FoundationsRL_RLBasics_error_decomposition_optimistic
-- name    : FoundationsRL.RLBasics.error_decomposition_optimistic
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-18T05:03:38.82538+00:00
-- url     : https://prove2.me/theorems/da66fa18-f80e-4017-8e90-83798388182c
-- title:
--   Lemma 15 — Error decomposition for optimistic policies
-- statement:
--   This lemma is the analytical core that makes optimism-based algorithms (like UCB-VI) work: it bounds the sub-optimality of a greedy policy purely in terms of how self-consistent (under the Bellman operator) its driving $Q$-value estimates are.
--
--   Fix a finite-horizon episodic MDP $M$ and a sequence of $Q$-value estimates $\widehat Q_1,\dots,\widehat Q_H : S\times A \to \mathbb R$ (with the terminal convention $\widehat Q_H \equiv 0$, in the $0$-indexed convention of this mission) that are **optimistic**: $Q^{M,\star}_h(s,a) \le \widehat Q_h(s,a)$ for every layer $h<H$ and $(s,a)$ (Eq. (5.22)). Let $\widehat\pi$ be the deterministic policy greedy with respect to $\widehat Q$ at every layer. Then for every state $s$,
--
--   $$V^{M,\star}_1(s) - V^{M,\widehat\pi}_1(s) \le \sum_{h=1}^{H} \mathbb E^{M,\widehat\pi}_{s_h}\Big[\widehat Q_h(s_h,\widehat\pi_h(s_h)) - \big[T^M_h \widehat Q_{h+1}\big](s_h,\widehat\pi_h(s_h))\Big],$$
--
--   where the roll-in expectation is under $\widehat\pi$ **itself** (an *on-policy* guarantee), and the bracketed term at each layer is $\widehat Q_h$'s own Bellman residual against the *true* Bellman operator $T^M_h$. In words: however $\widehat Q$ was produced, as long as it is optimistic, the sub-optimality of its greedy policy is controlled additively (not exponentially) by how badly $\widehat Q$ fails to satisfy the true Bellman equation, evaluated only along the trajectories $\widehat\pi$ itself induces. This is exactly the guarantee UCB-VI's analysis instantiates, with $\widehat Q = Q^t$ built from the estimated transition model plus a confidence bonus.
--
--   **Formalization Note** Layers are $0$-indexed; the hypothesis `hterm` encodes the terminal convention $\widehat Q_H \equiv 0$ explicitly, and `hgreedy` encodes $\widehat\pi_h(s) \in \arg\max_a \widehat Q_h(s,a)$ via `IsArgmax`.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, p. 88, Lemma 15, Eq. (5.23)

import Mathlib
import Definitions.Def_FoundationsRL_RLBasics_Core

namespace FoundationsRL.RLBasics

/-- **Lemma 15 (Error decomposition for optimistic policies)** (Foster–Rakhlin,
arXiv:2312.16730v1, p. 88, Lemma 15, Eq. (5.23)): given optimistic `Q`-value estimates
`Qhat` (`Qstar ≤ Qhat` pointwise at every layer `< H`, Eq. (5.22), with the terminal
convention `Qhat H ≡ 0`) and the deterministic policy `πdet` greedy w.r.t. `Qhat`, the
sub-optimality of `πdet` at any `s` is controlled by the `πdet`-roll-in expectation of
`Qhat`'s Bellman residuals. -/
theorem error_decomposition_optimistic {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
    [DecidableEq S] [DecidableEq A] {H : ℕ} (M : EpisodicMDP S A H) (Qhat : ℕ → S → A → ℝ)
    (hterm : ∀ s a, Qhat H s a = 0) (hopt : ∀ h, h < H → ∀ s a, Qstar M h s a ≤ Qhat h s a)
    (πdet : ℕ → S → A) (hgreedy : ∀ h, h < H → ∀ s : S, IsArgmax (Qhat h s) (πdet h s))
    (s : S) :
    Vstar M 0 s - V M (detPolicy πdet) 0 s ≤
      ∑ h ∈ Finset.range H,
        stateExp M (detPolicy πdet) s h (fun sh =>
          Qhat h sh (πdet h sh) - bellmanOp M h (Qhat (h + 1)) sh (πdet h sh)) := by sorry

end FoundationsRL.RLBasics
