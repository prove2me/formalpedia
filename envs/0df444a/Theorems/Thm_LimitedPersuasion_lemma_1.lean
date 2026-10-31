-- Prove2me | Theorems.Thm_LimitedPersuasion_lemma_1
-- name    : LimitedPersuasion.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:24:39.098982+00:00
-- url     : https://prove2.me/theorems/850c5e5a-683b-4030-afd4-773e87c14250
-- title:
--   Lemma 1 — an optimal $k$-signal scheme can be taken direct and persuasive, recommending $k$ distinct actions (the first $k$ in symmetric instances)
-- statement:
--   Consider an instance with $n$ actions and $k$ signals, $2\le k\le n$, where the receiver best responds to every signal and breaks ties in favour of the sender.
--
--   1. There exist an optimal scheme $\varphi$ with $k$ signals and $k$ distinct actions $a(1),\dots,a(k)$ such that $\varphi$ is direct and persuasive: signal $\sigma$ recommends $a(\sigma)$, the receiver has no incentive to deviate,
--   $$\mathbb E[\varrho(\theta_{a(\sigma)})\mid\sigma]\ \ge\ \mathbb E[\varrho(\theta_i)\mid\sigma]\quad\text{for all }\sigma\text{ and }i,$$
--   and the sender's utility $u_S(\varphi)$ equals the utility when the receiver follows the recommendation.
--   2. In a symmetric instance there is an optimal direct and persuasive scheme in which the sender recommends the actions $[k]$ (signal $j$ recommends action $j$), again with $u_S(\varphi)$ equal to the utility of following the recommendation.
--
--   This revelation-principle-type statement is what allows §3.1 to work with direct persuasive schemes recommending from $[k]$ only.
--
--   **Formalization Note** Optimality is against every $k$-signal scheme, with the tie-broken best-response utility $u_S$ on both sides. Persuasiveness is stated with the joint (unnormalized) utilities $w_\sigma(i)$.
--
--   Differences from the source:
--   - reading: optimal scheme, receiver best responds with ties broken for the sender → `IsOptimal`: $u_S(\varphi)\ge u_S(\psi)$ for every $k$-signal scheme $\psi$, $u_S=\sum_\sigma\max_{i\in BR(\sigma)}v_\sigma(i)$; reason: the paper's definition, made explicit; its second-level fixed tie-breaking rule does not change $u_S$
--   - reading: direct scheme (each signal recommends an action) → a recommendation map $a$ together with $u_S(\varphi)=\sum_\sigma v_\sigma(a(\sigma))$; reason: the receiver follows the recommendation in the paper's direct schemes, and the proof's scheme recommends the tie-broken best response
--   - generalization: second sentence under the standing assumption that all types are distinct → symmetry only; reason: distinctness is not used, so the statement specializes to the paper's
--   - encoding: type sets $\Theta_i$, signals $\Sigma$ with $|\Sigma|=k$, distribution over $\Theta$, recommending the actions from $[k]$ → one finite type set $T$, states $\mathrm{Fin}\,n\to T$, signals $\mathrm{Fin}\,k$, prior a weight function, signal $j$ recommends action $j$; reason: Lean convention, same instances up to relabelling signals
-- source:
--   Gradwohl–Hahn–Hoefer–Smorodinsky, Algorithms for Persuasion with Limited Communication, arXiv:2007.12489v2, Lemma 1, §2 "Direct and Persuasive", p.5 (proof App. A, p.24)

import Mathlib
import Definitions.Def_LimitedPersuasion_Model

namespace LimitedPersuasion

/-- **Lemma 1**, Gradwohl–Hahn–Hoefer–Smorodinsky, *Algorithms for Persuasion with Limited
Communication*, arXiv:2007.12489v2, §2 "Direct and Persuasive", p.5 (proof App. A, p.24).

1. There exists an optimal scheme with `k` signals that is direct and persuasive and uses the
   signals to recommend `k` distinct actions `a : Fin k → Fin n` (injective).
2. In symmetric instances, there is an optimal direct and persuasive scheme in which the sender
   recommends the actions from `[k]` (signal `j` recommends action `j`).

In both parts "direct" also means that the recommended action is what the receiver's tie-broken
best response yields: the sender's utility `u_S(φ)` equals the utility when the receiver follows
the recommendation.

**Formalization Note.** Optimality is against every `k`-signal scheme, with best-response
utilities (`Instance.IsOptimal`). `[NeZero n]` follows from `2 ≤ k ≤ n`. Neither part assumes
distinct types. -/
theorem lemma_1 {T : Type*} [Fintype T] [DecidableEq T] {n k : ℕ} [NeZero n]
    (I : Instance T n) (hk : 2 ≤ k) (hkn : k ≤ n) :
    (∃ (φ : (Fin n → T) → Fin k → ℝ) (a : Fin k → Fin n), Function.Injective a ∧
      I.IsOptimal φ ∧ I.Persuasive φ a ∧ I.uS φ = I.followS φ a) ∧
    (I.IsSymmetric → ∃ φ : (Fin n → T) → Fin k → ℝ,
      I.IsOptimal φ ∧ I.Persuasive φ (Fin.castLE hkn) ∧
        I.uS φ = I.followS φ (Fin.castLE hkn)) := by sorry

end LimitedPersuasion
