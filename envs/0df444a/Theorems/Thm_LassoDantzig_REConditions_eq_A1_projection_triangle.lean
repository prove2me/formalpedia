-- Prove2me | Theorems.Thm_LassoDantzig_REConditions_eq_A1_projection_triangle
-- name    : LassoDantzig.REConditions.eq_A1_projection_triangle
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T10:08:14.055131+00:00
-- url     : https://prove2.me/theorems/5e43d02c-57df-4482-a882-7c345c28ee12
-- title:
--   (A.1) — Projection triangle inequality over the block partition of $J_0^c$
-- statement:
--   Let $X\in\mathbb R^{n\times M}$, $\delta\in\mathbb R^M$, $J_0\subseteq\{1,\dots,M\}$, and let $J_0^c=J_1\cup\dots\cup J_K$ ($K\ge1$) be any partition of $J_0^c$ into pairwise disjoint (possibly empty) blocks. Put $J_{01}=J_0\cup J_1$ and let $P_{01}$ be the orthogonal projector in $\mathbb R^n$ onto the linear span of the columns of $X_{J_{01}}$. Then
--
--   $$
--   |P_{01}X\delta|_2\ \ge\ |P_{01}X\delta_{J_{01}}|_2-\Big|\sum_{k=2}^KP_{01}X\delta_{J_k}\Big|_2
--   \ =\ |X\delta_{J_{01}}|_2-\Big|\sum_{k=2}^KP_{01}X\delta_{J_k}\Big|_2
--   \ \ge\ |X\delta_{J_{01}}|_2-\sum_{k=2}^K|P_{01}X\delta_{J_k}|_2 .
--   $$
--
--   This is the first step of the proof of Lemma 4.1: it isolates the contribution of the leading block $J_{01}$ from that of the tail blocks.
--
--   **Formalization Note** The paper states (A.1) for the specific sorted partition; it holds for every partition, which is how it is stated here. $n\ge1$ and $M\ge2$ are the paper's standing assumptions. $P_{01}$ acts on $\mathbb R^n$ (the paper's "$\mathbb R^M$" on p. 9 is a slip).
-- source:
--   Bickel, Ritov and Tsybakov, Simultaneous Analysis of Lasso and Dantzig Selector, arXiv:0801.1095v3, p. 19, Appendix A, Eq. (A.1)

import Mathlib
import Definitions.Def_LassoDantzig_REConditions_RE
import Definitions.Def_LassoDantzig_REConditions_RestrictedEigenvalues

namespace LassoDantzig.REConditions

/-- **(A.1)**, Bickel–Ritov–Tsybakov, arXiv:0801.1095v3, Appendix A, p. 19. For any partition
`J0ᶜ = J 1 ∪ ⋯ ∪ J K` and `P01` the orthogonal projector in `ℝⁿ` onto the span of the columns
of `X_{J01}`, `J01 = J0 ∪ J 1`:
`|P01 Xδ|₂ ≥ |P01 X δ_{J01}|₂ − |∑_{k=2}^K P01 X δ_{Jk}|₂ = |X δ_{J01}|₂ − |∑_{k=2}^K P01 X δ_{Jk}|₂
≥ |X δ_{J01}|₂ − ∑_{k=2}^K |P01 X δ_{Jk}|₂`. -/
theorem eq_A1_projection_triangle {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ)
    (hn : 1 ≤ n) (hM : 2 ≤ M)
    (δ : Fin M → ℝ) (J0 : Finset (Fin M)) (J : ℕ → Finset (Fin M)) (K : ℕ)
    (hJ : IsBlockPartition J0ᶜ J K) :
    projNorm X (J0 ∪ J 1) (X.mulVec (restrict δ (J0 ∪ J 1))) -
        ‖∑ k ∈ Finset.Icc 2 K,
          (colSpan X (J0 ∪ J 1)).starProjection (WithLp.toLp 2 (X.mulVec (restrict δ (J k))))‖
      ≤ projNorm X (J0 ∪ J 1) (X.mulVec δ) ∧
    projNorm X (J0 ∪ J 1) (X.mulVec (restrict δ (J0 ∪ J 1))) =
      euclNorm (X.mulVec (restrict δ (J0 ∪ J 1))) ∧
    euclNorm (X.mulVec (restrict δ (J0 ∪ J 1))) -
        ∑ k ∈ Finset.Icc 2 K, projNorm X (J0 ∪ J 1) (X.mulVec (restrict δ (J k)))
      ≤ euclNorm (X.mulVec (restrict δ (J0 ∪ J 1))) -
        ‖∑ k ∈ Finset.Icc 2 K,
          (colSpan X (J0 ∪ J 1)).starProjection (WithLp.toLp 2 (X.mulVec (restrict δ (J k))))‖ := by sorry

end LassoDantzig.REConditions
