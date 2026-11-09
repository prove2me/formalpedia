-- Prove2me | Theorems.Thm_FourBlockIP_FPT_lemma_1
-- name    : FourBlockIP.FPT.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:38:29.44298+00:00
-- url     : https://prove2.me/theorems/039a2fe8-95a0-4e05-95ed-d13ae5e0012c
-- title:
--   Lemma 1 — convex extensibility on a dilated lattice subspace
-- statement:
--   Let $h:\mathbb Z^m\to\mathbb R$ be integer midpoint convex, let $k\ge0$ be an integer, and let $S\subseteq\mathbb R^m$ be a linear subspace of dimension $d$ with $2d\le k$. Then
--
--   $$z\longmapsto h(kz)\quad\text{is convex extensible on }\mathbb Z^m\cap S.$$
--
--   The extension is defined on the entire real ambient space and takes values in $\mathbb R\cup\{+\infty\}$, never $-\infty$. This supplies the structural subspace extension needed by the algorithmic framework, including the zero-dimensional case.
--
--   Differences from the source:
--   - encoding: Euclidean spaces and integer vectors with one-based coordinates → functions on Fin types with zero-based coordinates; reason: finite reindexing changes no instance
--   - encoding: convex functions into the reals extended by positive infinity → EReal functions with bottom excluded and a convex real-height epigraph; reason: this is the same extended-real convexity notion without imposing continuity
-- source:
--   Martin Koutecký, Alexandra Lassota, Koen Ligthart, 4-Block Integer Programming is in FPT, STOC 2027 submission #392 (October 2026), Lemma 1, p. 3; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/392.pdf

import Mathlib
import Definitions.Def_FourBlockIP_FPT_Convexity

namespace FourBlockIP.FPT

/-- Lemma 1, pp. 3,5. The extension takes no value -∞. -/
theorem lemma_1 {m : ℕ} (f : (Fin m → ℤ) → ℝ) (k : ℕ)
    (S : Submodule ℝ (Fin m → ℝ)) (hf : IntMidpointConvex f)
    (hd : 2 * Module.finrank ℝ S ≤ k) :
    ConvexExtensibleOn (fun z => (f (k • z) : EReal)) {z | castVec z ∈ S} := by sorry

end FourBlockIP.FPT
