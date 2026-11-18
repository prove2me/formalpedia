-- Prove2me | Theorems.Thm_KoanaKPaths_Main_exterior_word_coordinates
-- name    : KoanaKPaths.Main.exterior_word_coordinates
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T01:18:58.685356+00:00
-- url     : https://prove2.me/theorems/99f9889d-3f65-4408-a94d-d4b78230c4a2
-- title:
--   Exterior word coordinates are determinant minors
-- statement:
--   Let $v_1,\ldots,v_d\in\mathbb Z^k$ be a finite sequence of vectors, and let $S$ be a subset of the $k$ basis positions. Evaluate their product by repeated right multiplication in subset coordinates. Its coordinate at $S$ is zero unless $|S|=d$. In the latter case, write $s_1<\cdots<s_d$ for the increasing enumeration of $S$. Then
--
--   $$
--   (v_1\wedge\cdots\wedge v_d)_S=\det\bigl[v_j(s_i)\bigr]_{i,j=1}^{d}.
--   $$
--
--   If every vector entry has absolute value at most one, each coordinate additionally satisfies
--
--   $$
--   \bigl|(v_1\wedge\cdots\wedge v_d)_S\bigr|\le d!.
--   $$
--
--   This is the coordinate form of the paper's exterior-product determinant identity, including its minors and homogeneous support. For $d=k$, the full-subset coordinate is the determinant used in the estimator. The coefficient bound supplies the integer-size estimate in the implementation.
-- source:
--   Tomohiro Koana, Approximate Counting of k-Paths in O*(2^k) Time, STOC 2027 submission #953, Section 2, printed p. 5 / PDF p. 6 (exterior coordinates, right multiplication by a vector, determinant identity), and Section 3.2, printed p. 9 / PDF p. 10 (factorial coefficient bound). https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/953.pdf

import Definitions.Def_KoanaKPaths_ExteriorCoordinates

theorem KoanaKPaths.Main.exterior_word_coordinates (k : ℕ) (vs : List (Fin k → ℤ))
    (S : Finset (Fin k)) :
    (KoanaKPaths.ExteriorCoordinates.wordCoordinates vs S =
      if hs : S.card = vs.length then
        Matrix.det (Matrix.of (fun r c : Fin vs.length =>
          (vs.getD c.val (fun _ => 0)) (S.orderEmbOfFin hs r)))
      else 0) ∧
    ((∀ v ∈ vs, ∀ r, |v r| ≤ 1) →
      |KoanaKPaths.ExteriorCoordinates.wordCoordinates vs S| ≤ (vs.length.factorial : ℤ)) := by sorry
