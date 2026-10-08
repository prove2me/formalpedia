-- Prove2me | Theorems.Thm_FoundationsRL_FuncApprox_optimism_and_elliptic_bound_v2
-- name    : FoundationsRL.FuncApprox.optimism_and_elliptic_bound_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T06:19:23.61+00:00
-- url     : https://prove2.me/theorems/ca4e28b9-b828-4cfe-890a-605e04132023
-- title:
--   Lemma 30 — BiLinUCB optimism and elliptic-norm bound (v2: one shared constant)
-- statement:
--   This is **Lemma 30** of Foster & Rakhlin (arXiv:2312.16730v1, p. 142), a deterministic consequence of the confidence-set event of Lemma 29, used in the proof of Proposition 47.
--
--   Suppose the MDP $M^\star$ admits, for the finite value-function class $\mathcal Q$ (realized via `qeval`), a bilinear factorization of the Bellman residual, $E_h(\pi,Q)=\langle X_h(\pi),W_h(Q)\rangle$ with $X_h(\pi),W_h(Q)\in\mathbb R^d$ for all $\pi\in\Pi^{\rm rns}$, $Q\in\mathcal Q$, $h\in[H]$ (Eq. (7.24)), and that $Q^{M^\star,\star}\in\mathcal Q$ (encoded by `q0`). Fix any history, batch size $n$, threshold $\beta$, constant $C$ and iteration $k$ at which the event of Lemma 29 holds with constant $C$: every $Q$ in the confidence set $\mathcal Q_k$ satisfies $\sum_{i<k}E_h(\pi_i,Q)^2\le C\beta$ at every layer, where $\pi_i$ is the policy BiLinUCB plays at iteration $i$, and $Q^{M^\star,\star}\in\mathcal Q_k$. Then:
--   1. every $Q\in\mathcal Q_k$ satisfies, for every $h\in[H]$,
--   $$\|W_h(Q)\|^2_{\Sigma^k_h}=\sum_{i<k}\langle X_h(\pi_i),W_h(Q)\rangle^2\le C\beta,\qquad\Sigma^k_h=\sum_{i<k}X_h(\pi_i)X_h(\pi_i)^\top$$
--   (Eq. (7.30));
--   2. the optimistic value function $Q_k=\arg\max_{Q\in\mathcal Q_k}\mathbb E_{s_1\sim d_1}[Q_1(s_1,\pi_Q(s_1))]$ selected by BiLinUCB satisfies $\mathbb E_{s_1\sim d_1}[(Q_k)_1(s_1,\pi_{Q_k}(s_1))]\ge f^{M^\star}(\pi_{M^\star})$ (Eq. (7.31)).
--
--   **Formalization Note.** The retired version fixed an absolute constant $C'$ for the conclusion (7.30) *before* universally quantifying the constant $C$ of the hypothesis (7.27), so $C'$ had to dominate an arbitrary $C$, which is false (the accepted disproof). In the book both $\lesssim$ share one constant: the proof of part 1 is the identity $\|W_h(Q)\|^2_{\Sigma^k_h}=\sum_{i<k}E_h(\pi_i,Q)^2$, so the new statement concludes $\le C\beta$ with the same $C$. The elliptic norm is expressed through the identity $\|v\|^2_{\Sigma}=\sum_x\langle x,v\rangle^2$ (`elliptNormSq`) without matrix machinery. The lemma is purely algebraic, so the Section 7 reward normalization and the $[0,1]$ range of the class are not needed and are not assumed (the statement is slightly more general than the printed one); the history, $n$, $\beta$, $C$ and $k$ are arbitrary, and $\arg\max$ ties are broken by the first maximizer.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, p. 142, Lemma 30 (Eqs. (7.29)–(7.31))

import Mathlib
import Definitions.Def_FoundationsRL_RLBasics_Core
import Definitions.Def_FoundationsRL_RLBasics_UCBVI
import Definitions.Def_FoundationsRL_FuncApprox_Core
import Definitions.Def_FoundationsRL_FuncApprox_BiLinUCB

namespace FoundationsRL.FuncApprox

open FoundationsRL.RLBasics

/-- **Lemma 30** (Foster–Rakhlin, arXiv:2312.16730v1, p. 142, Lemma 30): whenever, for a
fixed iteration `k`, (a) `M⋆` admits the Bellman-rank bilinear factorization `(X, W)` of
Eq. (7.24) for the value-function class realized by `qeval`, and (b) the event of Lemma 29
holds at `k` with constant `C` — every retained `Q ∈ 𝒬_k` has
`Σ_{i<k} E_h(π_i, Q)² ≤ C·β` at every layer (Eq. (7.27)), and the realizable `q0 = Q^{M⋆,⋆}` is
itself retained — then: (1) every retained `Q ∈ 𝒬_k` has `‖W_h(Q)‖²_{Σ^k_h} ≤ C·β` for the
Gram matrix `Σ^k_h = Σ_{i<k} X_h(π_i)X_h(π_i)ᵀ` (Eq. (7.30), with the *same* constant: the
book's proof is the identity `‖W_h(Q)‖²_{Σ^k_h} = Σ_{i<k} ⟨X_h(π_i),W_h(Q)⟩² = Σ_{i<k} E_h(π_i,Q)²`);
(2) the optimistic value function `Q_k` selected by BiLinUCB at iteration `k` has initial-state
value at least `f^{M⋆}(π_{M⋆})` (Eq. (7.31)).

Corrected replacement of `optimism_and_elliptic_bound`: the retired statement fixed an
absolute constant `C'` *before* universally quantifying the constant `C` of hypothesis (7.27),
so `C'` had to dominate an arbitrary `C`, which is false; the two `≲` in Lemma 29/30 share one
constant. -/
theorem optimism_and_elliptic_bound_v2
    {S A : Type} [Fintype S] [Fintype A] [Nonempty A] [DecidableEq S] [DecidableEq A]
    {H : ℕ} (M : EpisodicMDP S A H) {Qc : Type} [Fintype Qc] [Nonempty Qc]
    (qeval : Qc → ℕ → S → A → ℝ) (q0 : Qc)
    (_hq0 : qeval q0 = fun h s a => if h < H then Qstar M h s a else 0)
    (d : ℕ) (X : Policy S A H → ℕ → Fin d → ℝ) (W : (ℕ → S → A → ℝ) → ℕ → Fin d → ℝ)
    (_hfact : ∀ π, IsPolicy H π → ∀ Qf : Qc, ∀ h : ℕ, h < H →
        bellmanResidual M π h (qeval Qf) = ∑ j : Fin d, X π h j * W (qeval Qf) h j)
    (hist : List (Trajectory S A H)) (n : ℕ) (β C : ℝ) (k : ℕ)
    (_hconf : ∀ Qf ∈ confSet M qeval hist n β k, ∀ h : Fin H,
        ∑ i ∈ Finset.range k,
          (bellmanResidual M (iterPolicy M qeval hist n β i) h.1 (qeval Qf)) ^ 2 ≤ C * β)
    (_hq0mem : q0 ∈ confSet M qeval hist n β k) :
    (∀ Qf ∈ confSet M qeval hist n β k, ∀ h : Fin H,
        elliptNormSq
          ((List.range k).map (fun i => X (iterPolicy M qeval hist n β i) h.1))
          (W (qeval Qf) h.1) ≤ C * β)
    ∧ initValue M qeval (bestQ M qeval hist n β k) ≥ ∑ s : S, M.d1 s * Vstar M 0 s := by sorry

end FoundationsRL.FuncApprox
