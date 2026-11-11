-- Prove2me | Theorems.Thm_LogitRankDistill_lemma_5_1
-- name    : LogitRankDistill.lemma_5_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:58:37.510444+00:00
-- url     : https://prove2.me/theorems/be2fbdf1-8044-481e-9190-2fac60e6f260
-- title:
--   Lemma 5.1 — an approximately rank-d sequence cannot be fooled more than C·d·log(BRd/γ) times
-- statement:
--   There is a constant $C_{5.1}>0$ such that the following holds. Fix $d,N\in\mathbb N$ and $B,R,\gamma>0$. Let $L_1,\dots,L_T\in\mathbb R^N$ and $J_1,\dots,J_T\in[N]$ be such that $L_1,\dots,L_T$ are $(B,R,\gamma/2)$-bounded of rank $d$ with respect to $J_1,\dots,J_T$ (Definition 5.1), and let $Q_t=\frac1{t-1}\sum_{s=1}^{t-1}\delta_{J_s}$. If for each $t\in[T]$
--   $$|L_t(J_t)|\ge\gamma\sqrt{C_{5.1}\,d\log(RB/\gamma)}\quad\text{and}\quad\|L_t\|_{2,Q_t}\le\gamma,$$
--   then $T\le C_{5.1}\,d\log(BRd/\gamma)$.
--   This elliptic-potential count is what bounds the number of epochs of Algorithm 1 that can end with a Line 15 update (Lemma 5.6).
--
--   **Formalization Note.** Indices are 0-based: `t : Fin T` is the paper's $t+1$ and $Q$ at Lean index $t\ge1$ is $\frac1t\sum_{s<t}\delta_{J_s}$. $\log$ and $\sqrt{\ }$ are `Real.log` and `Real.sqrt` as printed (no condition $RB\ge\gamma$ is added).
--
--   Differences from the source:
--   - reading: ‖L_1‖_{2,Q_1} ≤ γ with Q_1 = (1/0)·(empty sum) → no norm condition at t = 1; reason: Q_1 is undefined; the proof uses the condition only for t ≥ 2
--   - reading: √(C d log(RB/γ)) and log(BRd/γ) for all B, R, γ > 0 → Real.sqrt and Real.log (√ of a negative number is 0; log x = 0 for x ≤ 0); reason: the printed expressions are undefined when RB < γ; no hypothesis RB ≥ γ is added
--   - encoding: t ∈ [T], J_t ∈ [N] → t : Fin T (0-based), J t : Fin N; reason: index shift; same instances
-- source:
--   Golowich, Liu, Shetty, Provably Distilling from Modern Language Models via Low Logit Rank, manuscript of November 3, 2026 (arXiv:2512.09892; sha256 2ce0606e…), p. 21, Lemma 5.1

import Mathlib
import Definitions.Def_LogitRankDistill_Spanners

namespace LogitRankDistill

/-- **Lemma 5.1** (p. 21): there is a constant `C_{5.1} > 0` such that for all `d, N ∈ ℕ`,
`B, R, γ > 0`, vectors `L_1, …, L_T ∈ ℝ^N` and indices `J_1, …, J_T ∈ [N]` such that the `L_t`
are `(B, R, γ/2)`-bounded of rank `d` with respect to the `J_t`, if for each `t ∈ [T]`
`|L_t(J_t)| ≥ γ √(C_{5.1} d log(RB/γ))` and `‖L_t‖_{2,Q_t} ≤ γ` with
`Q_t = (1/(t−1)) ∑_{s<t} δ_{J_s}`, then `T ≤ C_{5.1} d log(BRd/γ)`. Indices are 0-based
(`t : Fin T` is the paper's `t + 1`); the norm condition is read as vacuous at the paper's `t = 1`
(where `Q_1 = (1/0)·0` is undefined). -/
theorem lemma_5_1 :
    ∃ C : ℝ, 0 < C ∧ ∀ (d N T : ℕ) (B R γ : ℝ), 0 < B → 0 < R → 0 < γ →
      ∀ (L : Fin T → Fin N → ℝ) (J : Fin T → Fin N),
        IsBoundedRankSeq B R (γ / 2) d L J →
        (∀ t : Fin T, γ * Real.sqrt (C * d * Real.log (R * B / γ)) ≤ |L t (J t)| ∧
          (1 ≤ (t : ℕ) →
            wnorm (fun i : Fin N =>
              (1 / (t : ℝ)) * ((Finset.univ.filter fun s : Fin T => s < t ∧ J s = i).card : ℝ))
              (L t) ≤ γ)) →
        (T : ℝ) ≤ C * d * Real.log (B * R * d / γ) := by sorry

end LogitRankDistill
