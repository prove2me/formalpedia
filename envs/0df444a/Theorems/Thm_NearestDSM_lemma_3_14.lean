-- Prove2me | Theorems.Thm_NearestDSM_lemma_3_14
-- name    : NearestDSM.lemma_3_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:20:21.306176+00:00
-- url     : https://prove2.me/theorems/72e09913-d5a5-4b4f-9684-d084177c568e
-- title:
--   Lemma 3.14 — the interval of admissible shifts (3.10)
-- statement:
--   Let $y\in\mathbb R^{2n-1}$ and suppose that $X=\mathrm{Mat}(\hat x+A^Ty)_+$ has the block form
--   $$
--   X=\begin{bmatrix}X^{R,C}&0\\0&X^{\bar R,\bar C}\end{bmatrix},\qquad Y=\mathrm{Mat}(\hat x+A^Ty)=\begin{bmatrix}Y^{R,C}&Y^{R,\bar C}\\Y^{\bar R,C}&Y^{\bar R,\bar C}\end{bmatrix}
--   $$
--   for a set $R$ of rows, not containing the last row, and a set $C$ of columns. Let $u^1$ be the vector with $u^1_i=-1$ for $i\in C$ and $u^1_{n+i}=1$ for $i\in R$, and $\tilde y:=y+tu^1$ with $t\in\mathbb R$. Then
--   $$
--   y\sim\tilde y\iff \max_{i,j}Y^{\bar R,C}_{ij}\le t\le-\max_{i,j}Y^{R,\bar C}_{ij}.
--   $$
--   This is the step used to move from a point of a class towards a vertex (Theorem 3.15).
--
--   **Formalization Note** The maxima are written as bounds over all entries of the block, so an empty block imposes no condition.
--
--   Differences from the source:
--   - reading: $u^1$ "defined as in (3.7) for the partition above" → the block $(R,C)$ does not contain the last row; reason: (3.7) has no coordinate for the last row, so $u^1$ is defined only for the block without it; exchanging the two blocks (and $t$ with $-t$) covers every partition
--   - generalization: "Let $X$ be disconnected" → not assumed; reason: the equivalence holds for every such pair $(R,C)$; the block form already makes $X$ disconnected except when $R$ and $C$ are both empty, where $u^1=0$ and both sides hold
--   - encoding: $\max$ over a block → $\forall$-bounds over its entries; reason: same condition for nonempty blocks, and no condition for an empty block
--   - encoding: size $n\ge1$ → `n + 1`; reason: Lean convention, same instances
-- source:
--   Hu, Im, Li & Wolkowicz, A Semismooth Newton-Type Method for the Nearest Doubly Stochastic Matrix Problem, arXiv:2107.09631v1, Lemma 3.14 and (3.10), p.19 ((2.2) p.7, (3.7) p.16)

import Mathlib
import Definitions.Def_NearestDSM_equivClass
import Definitions.Def_NearestDSM_shiftVec

namespace NearestDSM

/-- Hu, Im, Li & Wolkowicz, arXiv:2107.09631v1, Lemma 3.14, p.19. Let `y ∈ ℝ^{2n−1}`, and let `X = Mat(x̂ + Aᵀy)₊` have
the block form `X = [X^{R,C} 0; 0 X^{R̄,C̄}]` for subsets `R` (rows) and `C` (columns) as in (2.2),
with `Y = Mat(x̂ + Aᵀy)` partitioned alike. Let `ỹ := y + t u¹` for `t ∈ ℝ`, where `u¹` is defined
as in (3.7) for this partition (`u¹_i = −1` for `i ∈ C`, `u¹_{n+i} = 1` for `i ∈ R`). Then
`y ∼ ỹ ⟺ max_{i,j} Y^{R̄,C}_{ij} ≤ t ≤ −max_{i,j} Y^{R,C̄}_{ij}` (3.10).

**Formalization Note.** The last row `Fin.last n` is not in `R`: (3.7) has no coordinate for it,
so `u¹` is defined only for the block without the last row; swapping the two blocks covers every
partition. The two maxima are written as `∀`-bounds, so an empty block imposes no bound. The
hypothesis "X disconnected" is not assumed (the equivalence holds for every such pair `R`, `C`).
The paper's size `n` is `n + 1`. -/
theorem lemma_3_14 {n : ℕ} (Xh : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (y : Dual n) (R C : Set (Fin (n + 1)))
    (hR : Fin.last n ∉ R)
    (hblk : ∀ a b, (a ∈ R ∧ b ∉ C) ∨ (a ∉ R ∧ b ∈ C) → Xmat Xh y a b = 0) (t : ℝ) :
    y + t • shiftVec R C ∈ equivClass Xh y ↔
      (∀ a ∉ R, ∀ b ∈ C, Ymat Xh y a b ≤ t) ∧ (∀ a ∈ R, ∀ b ∉ C, t ≤ -Ymat Xh y a b) := by sorry

end NearestDSM
