-- Prove2me | Theorems.Thm_NearestDSM_lemma_3_7
-- name    : NearestDSM.lemma_3_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:21:00.311858+00:00
-- url     : https://prove2.me/theorems/7f37804b-8307-46a2-a511-4da05643555a
-- title:
--   Lemma 3.7 — equivalent vectors differ by a combination of $u^1,\dots,u^{K-1}$
-- statement:
--   Let $X=\mathrm{Mat}(\hat x+A^T\tilde y)_+$ have connected diagonal blocks $X^1,\dots,X^K$, the last one containing the last row, and let $U=[u^1\cdots u^K]$ be as in (3.6)–(3.7). If $y\sim\tilde y$, then
--   $$
--   \tilde y-y\in\mathrm{range}\big([u^1\ \cdots\ u^{K-1}]\big),
--   $$
--   the span of the first $K-1$ columns of $U$.
--
--   Equivalent vectors therefore differ only by shifting multipliers between the rows and columns of each block other than the last.
--
--   **Formalization Note** Blocks are the connected components of the bipartite graph of $X$, which is the same for $y$ and $\tilde y$.
--
--   Differences from the source:
--   - encoding: blocks $X^1,\dots,X^K$ of (3.2) "up to permutation", with $X^K$ the block of row $n$ → connected components of the bipartite graph of $X$, with the last block the component of the last row; reason: the same partition; a zero row or column is its own block, as on p.7
--   - encoding: size $n\ge1$ → `n + 1`; reason: Lean convention, same instances
-- source:
--   Hu, Im, Li & Wolkowicz, A Semismooth Newton-Type Method for the Nearest Doubly Stochastic Matrix Problem, arXiv:2107.09631v1, Lemma 3.7, p.16

import Mathlib
import Definitions.Def_NearestDSM_equivClass
import Definitions.Def_NearestDSM_blockShift
import Definitions.Def_NearestDSM_lastBlock

namespace NearestDSM

/-- Hu, Im, Li & Wolkowicz, arXiv:2107.09631v1, Lemma 3.7, p.16. If `y ∼ ỹ`, then `ỹ − y ∈ range([u¹ ⋯ u^{K−1}])`, the
span of the first `K − 1` columns of `U` (3.6)–(3.7).

**Formalization Note.** The blocks of `X = Mat(x̂ + Aᵀỹ)₊` are the connected components of its
bipartite graph; `u^κ` is `blockShift Xh ỹ κ`, and the excluded column `u^K` is that of the last
block, the component of the last row (`lastBlock`). Equivalent vectors have the same `X`, so the
partition is the same for `y` and `ỹ` (p.14). The paper's size `n` is `n + 1`. -/
theorem lemma_3_7 {n : ℕ} (Xh : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (yt y : Dual n) (hy : y ∈ equivClass Xh yt) :
    yt - y ∈ Submodule.span ℝ
      (Set.range fun κ : {κ : (bipGraph (Xmat Xh yt)).ConnectedComponent // κ ≠ lastBlock Xh yt} =>
        blockShift Xh yt κ.1) := by sorry

end NearestDSM
