-- Prove2me | Theorems.Thm_FourBlockIP_FPT_lemma_3
-- name    : FourBlockIP.FPT.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:38:35.051636+00:00
-- url     : https://prove2.me/theorems/76745dd7-341f-421e-bc86-e227c9ab27c1
-- title:
--   Lemma 3 — lattice midpoints in dilated integral polytopes
-- statement:
--   Let $P\subseteq\mathbb R^n$ be an integral polytope, let $k\ge0$ be an integer with $2\dim_{\rm aff}P\le k$, and let $z\in\mathbb Z^n$ lie in $kP$. If $z$ is not a vertex of $kP$, then
--
--   $$\exists q\in\mathbb Z^n\setminus\{0\}:\quad z-q\in kP,\quad z+q\in kP.$$
--
--   This is the lattice-midpoint property used for the convex-extension result. Empty polytopes and $k=0$ are retained; their nonvertex premise cannot hold.
--
--   Differences from the source:
--   - encoding: Euclidean spaces and integer vectors with one-based coordinates → functions on Fin types with zero-based coordinates; reason: finite reindexing changes no instance
-- source:
--   Martin Koutecký, Alexandra Lassota, Koen Ligthart, 4-Block Integer Programming is in FPT, STOC 2027 submission #392 (October 2026), Lemma 3, p. 5; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/392.pdf

import Mathlib
import Definitions.Def_FourBlockIP_FPT_Polyhedra

open scoped Pointwise

namespace FourBlockIP.FPT

/-- Lemma 3, p. 5. Includes k=0, empty polytopes, and non-full dimension. -/
theorem lemma_3 {n : ℕ} (P : Set (Fin n → ℝ)) (k : ℕ) (x : Fin n → ℤ)
    (hP : IntegralPolytope P) (hd : 2 * affDim P ≤ k)
    (hx : castVec x ∈ (k : ℝ) • P)
    (hnv : ¬ IsVertex (castVec x) ((k : ℝ) • P)) :
    ∃ p : Fin n → ℤ, p ≠ 0 ∧ castVec (x-p) ∈ (k : ℝ) • P ∧
      castVec (x+p) ∈ (k : ℝ) • P := by sorry

end FourBlockIP.FPT
