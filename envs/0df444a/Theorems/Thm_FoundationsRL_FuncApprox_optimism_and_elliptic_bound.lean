-- Prove2me | Theorems.Thm_FoundationsRL_FuncApprox_optimism_and_elliptic_bound
-- name    : FoundationsRL.FuncApprox.optimism_and_elliptic_bound
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-09-19T20:29:17.08396+00:00
-- url     : https://prove2.me/theorems/5b19965d-f7ff-4020-8589-eb34d83ea185
-- title:
--   Lemma 30 — BiLinUCB optimism and elliptic-norm bound
-- statement:
--   This is Lemma 30 of Foster & Rakhlin (arXiv:2312.16730v1, p. 142), a purely
--   deterministic consequence of the confidence-set event established by Lemma 29
--   (`FuncApprox.confidence_set_validity`), used directly in the proof of Proposition 47.
--
--   Suppose the true MDP $M^\star$ admits a Bellman-rank-$d$ bilinear factorization
--   $E_h(\pi,Q) = \langle X_h(\pi), W_h(Q)\rangle$ (Eq. (7.24), `FuncApprox.HasBellmanRankLE`)
--   for the value-function class $\mathcal Q$, and fix an iteration $k$ at which the event of
--   Lemma 29 holds: every $Q$ retained in $\mathcal Q_k$ has bounded true Bellman residual
--   along the policies $\pi_1,\dots,\pi_{k-1}$ actually played, and $Q^{M^\star,\star}$ is
--   itself retained. Then:
--
--   1. every $Q \in \mathcal Q_k$ has $W_h(Q)$ of bounded elliptic norm,
--      $$
--      \|W_h(Q)\|^2_{\Sigma^k_h} := \sum_{i<k} \langle X_h(\pi_i), W_h(Q)\rangle^2 \lesssim
--      \beta,
--      $$
--      with respect to the Gram matrix $\Sigma^k_h = \sum_{i<k} X_h(\pi_i)X_h(\pi_i)^\top$
--      built from the embeddings of the policies played so far;
--   2. the optimistic value function $Q_k$ that BiLinUCB selects at iteration $k$ has
--      initial-state value $\mathbb E_{s_1\sim d_1}[(Q_k)_1(s_1,\pi_{Q_k}(s_1))]$ at least
--      $f^{M^\star}(\pi^{M^\star})$, the optimal expected return.
--
--   **Formalization Note** The elliptic norm is expressed directly via the
--   sum-of-squared-inner-products identity `elliptNormSq`, avoiding `Matrix`/matrix-inverse
--   machinery; it agrees with the quadratic form $v \mapsto v^\top \Sigma v$ for
--   $\Sigma = \sum_x xx^\top$.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, p. 142, Lemma 30 (Eq. 7.29, 7.30, 7.31)

import Mathlib
import Definitions.Def_FoundationsRL_RLBasics_Core
import Definitions.Def_FoundationsRL_RLBasics_UCBVI
import Definitions.Def_FoundationsRL_FuncApprox_Core
import Definitions.Def_FoundationsRL_FuncApprox_BiLinUCB

namespace FoundationsRL.FuncApprox

open FoundationsRL.RLBasics

/-- **Lemma 30** (Foster–Rakhlin, arXiv:2312.16730v1, p. 142, Lemma 30): whenever, for a
fixed iteration `k`, (a) `M⋆` admits the Bellman-rank bilinear factorization `(X, W)` of
Eq. (7.24) for the value-function class realized by `qeval`, and (b) the confidence-set event
of Lemma 29 holds at `k` — i.e. every retained `Q ∈ Q_k` has bounded true Bellman residual
along `π_1,…,π_{k-1}`, and the realizable `q0` is itself retained — then: (1) every retained
`Q ∈ Q_k` has `W_h(Q)` of bounded elliptic norm with respect to the Gram matrix built from
`X_h(π_1),…,X_h(π_{k-1})`; (2) the optimistic value function `Q_k` BiLinUCB selects at
iteration `k` has initial-state value at least `f^{M⋆}(π^{M⋆})`. -/
theorem optimism_and_elliptic_bound :
    ∃ C' : ℝ, 0 < C' ∧
      ∀ {S A : Type} [Fintype S] [Fintype A] [Nonempty A] [DecidableEq S] [DecidableEq A]
        {H : ℕ} (M : EpisodicMDP S A H) {Qc : Type} [Fintype Qc] [Nonempty Qc]
        (qeval : Qc → ℕ → S → A → ℝ) (q0 : Qc)
        (_hq0 : qeval q0 = fun h s a => if h < H then Qstar M h s a else 0)
        (d : ℕ) (X : Policy S A H → ℕ → Fin d → ℝ) (W : (ℕ → S → A → ℝ) → ℕ → Fin d → ℝ)
        (_hfact : ∀ π, IsPolicy H π → ∀ Qf : Qc, ∀ h : ℕ, h < H →
            bellmanResidual M π h (qeval Qf) = ∑ j : Fin d, X π h j * W (qeval Qf) h j)
        (hist : List (Trajectory S A H)) (n : ℕ) (β C : ℝ) (k : ℕ),
        (∀ Qf ∈ confSet M qeval hist n β k, ∀ h : Fin H,
            ∑ i ∈ Finset.range k,
              (bellmanResidual M (iterPolicy M qeval hist n β i) h.1 (qeval Qf)) ^ 2 ≤ C * β) →
        q0 ∈ confSet M qeval hist n β k →
        (∀ Qf ∈ confSet M qeval hist n β k, ∀ h : Fin H,
            elliptNormSq
              ((List.range k).map (fun i => X (iterPolicy M qeval hist n β i) h.1))
              (W (qeval Qf) h.1) ≤ C' * β)
        ∧ initValue M qeval (bestQ M qeval hist n β k) ≥ ∑ s : S, M.d1 s * Vstar M 0 s := by sorry

end FoundationsRL.FuncApprox
