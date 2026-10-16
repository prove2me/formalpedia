-- Prove2me | Theorems.Thm_OAI_Paper256_matrix_compression_posSemidef_iff
-- name    : OAI.Paper256.matrix_compression_posSemidef_iff
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T19:03:15.97598+00:00
-- url     : https://prove2.me/theorems/975b6fc7-da0d-4eb7-b5e8-39a6ed9dedac
-- title:
--   A symmetric matrix with vanishing rows is positive semidefinite exactly when its compression is
-- statement:
--   Let $\iota$ be a finite index set, $S\subseteq\iota$ a subset, and $M=(M_{ij})_{i,j\in\iota}$ a real symmetric matrix. Suppose that every row of $M$ indexed outside $S$ vanishes: $M_{ij}=0$ for all $i\in\iota\setminus S$ and all $j\in\iota$. Let $M_{S,S}=(M_{ij})_{i,j\in S}$ be the principal submatrix on $S$. Then
--   $$M\succeq0\iff M_{S,S}\succeq0,$$
--   where $N\succeq0$ means that $N$ is symmetric and $v^\top Nv\ge0$ for every real vector $v$.
--
--   By symmetry the columns outside $S$ vanish as well, so after reordering $M$ is just $M_{S,S}$ padded with zeros, and the theorem says that such padding does not affect positive semidefiniteness. It is the basic tool for removing a common kernel from a linear matrix inequality: once all matrices of a pencil are known to vanish on certain coordinates, those coordinates can be deleted without changing the set where the pencil is positive semidefinite.
--
--   **Formalization Note** The subset $S$ is given by a decidable predicate `p` on the index type, and $M_{S,S}$ is `M.submatrix Subtype.val Subtype.val` on the subtype `{i // p i}`. Symmetry is the hypothesis `M.IsHermitian` (for real matrices Hermitian means symmetric).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/HyperbolicCones/CompressionBasic.lean#L33-L51

import Mathlib
import Definitions.Def_HyperbolicCones
import Definitions.Def_OAI_Analysis_HyperbolicCones_Model
import Definitions.Def_OAI_Analysis_HyperbolicCones_MatrixBasic
import Definitions.Def_OAI_Analysis_HyperbolicCones_MatrixLinear

open OAI OAI.Paper256
open Matrix
universe u v

theorem OAI.Paper256.matrix_compression_posSemidef_iff {ι : Type u} [Fintype ι]
    (p : ι → Prop) [DecidablePred p] (M : Matrix ι ι ℝ) (hM : M.IsHermitian)
    (hzero : ∀ i, ¬p i → ∀ j, M i j = 0) :
    M.PosSemidef ↔ (M.submatrix (Subtype.val : {i // p i} → ι) Subtype.val).PosSemidef := by sorry
