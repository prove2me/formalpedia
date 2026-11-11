-- Prove2me | Theorems.Thm_GroupIsoDepth_LowerBounds_theorem_5_7
-- name    : GroupIsoDepth.LowerBounds.theorem_5_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:40:28.090234+00:00
-- url     : https://prove2.me/theorems/6cd795b9-6c9c-4da4-b912-21552e7d21a2
-- title:
--   Theorem 5.7 ([dSP10, Thm 6], cf. [Mes85]) — an affine space of $k\times k$ matrices of rank $\le s$ has dimension $\le ks$
-- statement:
--   Over an arbitrary field $F$, if $A$ is an affine subspace of $F^{k\times k}$ and every matrix in $A$ has rank at most $s$, then $\dim A\le ks$.
--
--   Differences from the source:
--   - encoding: dim A of an affine subspace → Module.finrank F A.direction; A may be the empty subspace ⊥, whose direction is 0; reason: the empty case adds only the trivially true 0 ≤ ks
-- source:
--   Grochow, Kardeş, Levet, Group Isomorphism: Depth-2½ Circuits and Lower Bounds, STOC 2027 submission (manuscript sha256 cd6cacd4…), Theorem 5.7 (p. 38, PDF 39)

import Mathlib

namespace GroupIsoDepth.LowerBounds

/-- Theorem 5.7 ([dSP10, Theorem 6], cf. [Mes85]; printed p. 38, PDF 39). Over an arbitrary field
`F`, if `A` is an affine subspace of `F^{k×k}` and every matrix in `A` has rank at most `s`, then
`dim A ≤ k s`. (`dim A` is the dimension of the direction of `A`.) -/
theorem theorem_5_7 {F : Type*} [Field F] (k s : ℕ)
    (A : AffineSubspace F (Matrix (Fin k) (Fin k) F)) (hA : ∀ M ∈ A, M.rank ≤ s) :
    Module.finrank F A.direction ≤ k * s := by sorry

end GroupIsoDepth.LowerBounds
