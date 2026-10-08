-- Prove2me | Theorems.Thm_MinRankRecovery_Recovery_eq_3_6
-- name    : MinRankRecovery.Recovery.eq_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:17:23.995007+00:00
-- url     : https://prove2.me/theorems/5b6ce3a1-9919-42b2-8eda-a5d0e992b04b
-- title:
--   (3.5)–(3.6) — splitting a matrix into rank-3r blocks with Σ_{j≥2} ‖R_j‖_F ≤ ‖R_c‖_*/√(3r)
-- statement:
--   Let $r\ge1$ be an integer and $M$ a real $m\times n$ matrix. There are a number $N$ and matrices $R_1,\dots,R_N\in\mathbb R^{m\times n}$ such that
--   1. $M=\sum_{i=1}^N R_i$;
--   2. $\operatorname{rank}(R_i)\le 3r$ for every $i$;
--   3. $\langle R_i,R_j\rangle=0$ for $i\ne j$;
--   4. $\|M\|_*=\sum_{i=1}^N\|R_i\|_*$;
--   5. the column space of each $R_i$ lies in the column space of $M$, and the row space of each $R_i$ lies in the row space of $M$;
--   6. the tail obeys
--   $$\sum_{j\ge2}\|R_j\|_F\;\le\;\frac1{\sqrt{3r}}\,\|M\|_* .$$
--
--   In the paper, $M=R_c$ and the $R_i$ are the blocks of its singular value decomposition: with $R_c=U\operatorname{diag}(\sigma)V'$ and $I_i=\{3r(i-1)+1,\dots,3ri\}$, $R_i=U_{I_i}\operatorname{diag}(\sigma_{I_i})V_{I_i}'$. Inequality (3.5), $\sigma_k\le\frac1{3r}\sum_{j\in I_i}\sigma_j$ for $k\in I_{i+1}$, gives $\|R_{i+1}\|_F^2\le\frac1{3r}\|R_i\|_*^2$, and summing gives the first part of (3.6). In the proof of Theorem 3.3 this bound, combined with (3.4) and (2.1), controls the tail of the error by $\sqrt{2/3}\,\|R_0\|_F$.
--
--   **Formalization Note** Mathlib has no ordered rectangular singular value decomposition to name "the" blocks, so the statement asserts the existence of a decomposition with all the properties of the SVD blocks that the proof of Theorem 3.3 uses (items 1–6). Item 5 is encoded as inclusions of the ranges of `Matrix.toLin'` of $R_i$ and of $R_i^{\top}$ in those of $M$ and $M^{\top}$. Blocks are indexed by `Fin N` from $0$, so the paper's $j\ge2$ is the Lean index $\ge1$.
-- source:
--   Recht, Fazel & Parrilo, arXiv:0706.4138v1, §3, proof of Theorem 3.3, (3.5)–(3.6), pp. 13–14

import Mathlib
import Definitions.Def_HighDimStat_MatrixRank_Core

open HighDimStat.MatrixRank Matrix

namespace MinRankRecovery.Recovery

/-- (3.5)–(3.6), p. 13: every matrix `M` splits as `M = Σᵢ Rᵢ` into finitely many pairwise
orthogonal pieces of rank at most `3r`, with nuclear norms adding up, row and column spaces inside
those of `M`, and `Σ_{j ≥ 2} ‖R_j‖_F ≤ ‖M‖_* / √(3r)` (paper index `j ≥ 2` is Lean index `≥ 1`). -/
theorem eq_3_6 {m n : ℕ} (r : ℕ) (hr : 1 ≤ r) (M : Matrix (Fin m) (Fin n) ℝ) :
    ∃ (N : ℕ) (R : Fin N → Matrix (Fin m) (Fin n) ℝ),
      M = ∑ i, R i ∧
      (∀ i, (R i).rank ≤ 3 * r) ∧
      (∀ i j, i ≠ j → traceInner (R i) (R j) = 0) ∧
      nuclearNorm M = ∑ i, nuclearNorm (R i) ∧
      (∀ i, LinearMap.range (Matrix.toLin' (R i)) ≤ LinearMap.range (Matrix.toLin' M)) ∧
      (∀ i, LinearMap.range (Matrix.toLin' (R i)ᵀ) ≤ LinearMap.range (Matrix.toLin' Mᵀ)) ∧
      ∑ i ∈ Finset.univ.filter (fun i : Fin N => 1 ≤ (i : ℕ)), frobeniusNorm (R i) ≤
        1 / Real.sqrt (3 * r) * nuclearNorm M := by sorry

end MinRankRecovery.Recovery
