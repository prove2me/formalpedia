-- Prove2me | Theorems.Thm_GroupIsoDepth_LowerBounds_row_cube_properties
-- name    : GroupIsoDepth.LowerBounds.row_cube_properties
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:41:17.077686+00:00
-- url     : https://prove2.me/theorems/c379d58e-a33c-44e0-b8d2-576b6ee8cafc
-- title:
--   §5.2.1, row-cube properties 1–2 — a row-cube is affine with $\dim\mathcal F=\sum_j\dim U_j$ and $|\mathcal F|=2^{\dim\mathcal F}$; matrices in it are joined by one-row changes
-- statement:
--   Let $\mathcal F=A_1\times\dots\times A_k$ be a row-cube over $\mathbb F_2$.
--   1. If $A_j=a_j+U_j$ with $U_j$ a linear subspace of $\mathbb F_2^k$ (each $A_j$ nonempty), then $\mathcal F$ is an affine subspace of $\mathbb F_2^{k\times k}$: $\mathcal F=A+U$ with $U=U_1\times\dots\times U_k$. Consequently $\dim\mathcal F=\sum_{j=1}^k\dim U_j$ and $|\mathcal F|=2^{\dim\mathcal F}$.
--   2. Let $X=(x_1,\dots,x_k)$ and $Y=(y_1,\dots,y_k)$ belong to $\mathcal F$ and, for $t=0,\dots,k$, let $X^{(t)}=(y_1,\dots,y_t,x_{t+1},\dots,x_k)$. Every $X^{(t)}$ belongs to $\mathcal F$, $X^{(0)}=X$, $X^{(k)}=Y$, and consecutive matrices $X^{(t)},X^{(t+1)}$ differ in at most one row (row $t+1$).
--
--   Differences from the source:
--   - encoding: A_j = a_j + U_j → hypothesis ∀ j, (A j : Set _).Nonempty, with U_j = (A j).direction; reason: Mathlib's AffineSubspace allows the empty subspace; writing A_j = a_j + U_j presupposes A_j nonempty
--   - encoding: F = A + U is an affine subspace, dim F → ∃ P : AffineSubspace with ↑P = rowCube A and ↑P.direction = {U | ∀ j, U j ∈ (A j).direction}; dim = Module.finrank of the direction; |F| = Nat.card P; reason: the affine subspace A + U is the one through any point of F with direction U
--   - encoding: rows indexed 1, …, k; X^{(t)} takes rows 1..t from Y → rows indexed by Fin k = {0, …, k−1}; path t takes the rows j < t from Y; path t and path (t+1) agree off row index t; reason: 0-based indexing of the same matrices
-- source:
--   Grochow, Kardeş, Levet, Group Isomorphism: Depth-2½ Circuits and Lower Bounds, STOC 2027 submission (manuscript sha256 cd6cacd4…), §5.2.1 (p. 38, PDF 39)

import Mathlib
import Definitions.Def_GroupIsoDepth_LowerBounds_RowCubes

namespace GroupIsoDepth.LowerBounds

/-- §5.2.1, first and second properties of row-cubes (printed p. 38, PDF 39), over `𝔽₂`.
First: if every `A_j = a_j + U_j` is nonempty, the row-cube `F = A₁ × ⋯ × A_k` is an affine
subspace of `𝔽₂^{k×k}` with direction `U = U₁ × ⋯ × U_k`, so `dim F = Σ_j dim U_j` and
`|F| = 2^{dim F}`. Second: for `X, Y ∈ F` and `t = 0, …, k`, the matrix
`X^{(t)} = (y₁, …, y_t, x_{t+1}, …, x_k)` lies in `F`, `X^{(0)} = X`, `X^{(k)} = Y`, and consecutive
`X^{(t)}, X^{(t+1)}` differ in at most one row (row `t + 1`, i.e. index `t` from 0). -/
theorem row_cube_properties (k : ℕ) (A : Fin k → AffineSubspace (ZMod 2) (Fin k → ZMod 2)) :
    ((∀ j, (A j : Set (Fin k → ZMod 2)).Nonempty) →
      ∃ P : AffineSubspace (ZMod 2) (Matrix (Fin k) (Fin k) (ZMod 2)),
        (P : Set (Matrix (Fin k) (Fin k) (ZMod 2))) = rowCube A ∧
        (P.direction : Set (Matrix (Fin k) (Fin k) (ZMod 2))) = {U | ∀ j, U j ∈ (A j).direction} ∧
        Module.finrank (ZMod 2) P.direction = ∑ j, Module.finrank (ZMod 2) (A j).direction ∧
        Nat.card P = 2 ^ Module.finrank (ZMod 2) P.direction) ∧
    (∀ X ∈ rowCube A, ∀ Y ∈ rowCube A,
      let path : ℕ → Matrix (Fin k) (Fin k) (ZMod 2) := fun t j => if (j : ℕ) < t then Y j else X j
      (∀ t ≤ k, path t ∈ rowCube A) ∧ path 0 = X ∧ path k = Y ∧
        ∀ t < k, ∀ j : Fin k, (j : ℕ) ≠ t → path t j = path (t + 1) j) := by sorry

end GroupIsoDepth.LowerBounds
