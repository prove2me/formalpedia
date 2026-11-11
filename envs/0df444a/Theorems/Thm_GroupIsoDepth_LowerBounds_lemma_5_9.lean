-- Prove2me | Theorems.Thm_GroupIsoDepth_LowerBounds_lemma_5_9
-- name    : GroupIsoDepth.LowerBounds.lemma_5_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:41:21.765143+00:00
-- url     : https://prove2.me/theorems/07a7e320-64e0-4a7f-bc0a-6ba271852497
-- title:
--   Lemma 5.9 — ranks in a row-cube are contiguous; a row-cube with a rank-$s$ and no rank-$(s+1)$ matrix has all ranks $\le s$ and $\dim\le ks$
-- statement:
--   Let $\mathcal F=A_1\times\dots\times A_k$ be a row-cube over a field $F$.
--   1. The set of ranks of matrices occurring in $\mathcal F$ is a contiguous set of integers: if $X,Y\in\mathcal F$ and $\mathrm{rank}\,X\le r\le\mathrm{rank}\,Y$, then some $Z\in\mathcal F$ has rank $r$.
--   2. In particular, if $\mathcal F$ contains at least one rank-$s$ matrix but no rank-$(s+1)$ matrix, then every matrix in $\mathcal F$ has rank at most $s$; consequently $\dim_F\mathcal F\le ks$.
--
--   Differences from the source:
--   - reading: the set of ranks of matrices occurring in F is a contiguous set of integers → ∀ X Y ∈ F, ∀ r, rank X ≤ r ≤ rank Y → ∃ Z ∈ F, rank Z = r; reason: the definition of a contiguous set of integers
--   - encoding: dim_F F → Module.finrank F of the direction of affineSpan F (rowCube A); reason: a nonempty row-cube is an affine subspace (§5.2.1), so it equals its affine span; the hypothesis of clause 2 makes F nonempty
--   - encoding: affine subspaces A_j → Mathlib AffineSubspace, possibly ⊥; reason: an empty factor gives the empty row-cube, for which clause 1 is vacuous and clause 2's hypothesis fails
-- source:
--   Grochow, Kardeş, Levet, Group Isomorphism: Depth-2½ Circuits and Lower Bounds, STOC 2027 submission (manuscript sha256 cd6cacd4…), Lemma 5.9 (pp. 38–39, PDF 39–40)

import Mathlib
import Definitions.Def_GroupIsoDepth_LowerBounds_RowCubes

namespace GroupIsoDepth.LowerBounds

/-- Lemma 5.9 (printed pp. 38–39, PDF 39–40). Let `F = A₁ × ⋯ × A_k` be a row-cube over a field `F`.
1. The set of ranks of matrices in `F` is a contiguous set of integers: if `X, Y ∈ F` and
   `rank X ≤ r ≤ rank Y`, some `Z ∈ F` has rank `r`.
2. If `F` contains a rank-`s` matrix but no rank-`(s+1)` matrix, then every matrix in `F` has rank
   at most `s`, and `dim F ≤ k s` (`dim F` the dimension of the affine span of `F`). -/
theorem lemma_5_9 {F : Type*} [Field F] (k : ℕ) (A : Fin k → AffineSubspace F (Fin k → F)) :
    (∀ X ∈ rowCube A, ∀ Y ∈ rowCube A, ∀ r : ℕ, X.rank ≤ r → r ≤ Y.rank →
      ∃ Z ∈ rowCube A, Z.rank = r) ∧
    (∀ s : ℕ, (∃ X ∈ rowCube A, X.rank = s) → (∀ X ∈ rowCube A, X.rank ≠ s + 1) →
      (∀ X ∈ rowCube A, X.rank ≤ s) ∧
        Module.finrank F (affineSpan F (rowCube A)).direction ≤ k * s) := by sorry

end GroupIsoDepth.LowerBounds
