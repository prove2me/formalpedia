-- Prove2me | Theorems.Thm_MinRankRecovery_Recovery_lemma_3_4
-- name    : MinRankRecovery.Recovery.lemma_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:17:24.296891+00:00
-- url     : https://prove2.me/theorems/19b3d4f5-4c72-4d70-9edf-e198138cef3a
-- title:
--   Lemma 3.4 — B = B₁ + B₂ with rank B₁ ≤ 2 rank A, AB₂′ = 0, A′B₂ = 0, ⟨B₁, B₂⟩ = 0
-- statement:
--   Let $M$ and $N$ be real $m\times n$ matrices, and let $\langle X,Y\rangle=\operatorname{Tr}(X^{\top}Y)$ be the trace inner product. There exist matrices $N_1,N_2\in\mathbb R^{m\times n}$ such that
--   1. $N=N_1+N_2$;
--   2. $\operatorname{rank}(N_1)\le 2\operatorname{rank}(M)$;
--   3. $MN_2^{\top}=0$ and $M^{\top}N_2=0$;
--   4. $\langle N_1,N_2\rangle=0$.
--
--   The lemma splits $N$ into a part of rank comparable to that of $M$ and a part to which Lemma 2.3 applies together with $M$. It is the key decomposition in the proof of Theorem 3.3, where it is applied with $M=X_0$ and $N$ the error $X^*-X_0$.
--
--   **Formalization Note** The paper names the matrices $A$, $B$, $B_1$, $B_2$; here they are $M$, $N$, $N_1$, $N_2$. The inner product is `traceInner` of the referenced module.
-- source:
--   Recht, Fazel & Parrilo, arXiv:0706.4138v1, Lemma 3.4, pp. 12–13

import Mathlib
import Definitions.Def_HighDimStat_MatrixRank_Core

open HighDimStat.MatrixRank Matrix

namespace MinRankRecovery.Recovery

/-- Lemma 3.4, pp. 12–13: for matrices `M`, `N` of the same dimensions there are `N₁`, `N₂` with
`N = N₁ + N₂`, `rank N₁ ≤ 2 rank M`, `M N₂ᵀ = 0`, `Mᵀ N₂ = 0` and `⟨N₁, N₂⟩ = 0`. -/
theorem lemma_3_4 {m n : ℕ} (M N : Matrix (Fin m) (Fin n) ℝ) :
    ∃ N₁ N₂ : Matrix (Fin m) (Fin n) ℝ,
      N = N₁ + N₂ ∧ N₁.rank ≤ 2 * M.rank ∧ M * N₂ᵀ = 0 ∧ Mᵀ * N₂ = 0 ∧
        traceInner N₁ N₂ = 0 := by sorry

end MinRankRecovery.Recovery
