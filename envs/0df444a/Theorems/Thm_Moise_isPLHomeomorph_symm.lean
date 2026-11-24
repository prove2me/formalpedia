-- Prove2me | Theorems.Thm_Moise_isPLHomeomorph_symm
-- name    : Moise.isPLHomeomorph_symm
-- status  : Open
-- author  : @wojtek_politarczyk
-- created : 2026-11-24T18:29:44.514497+00:00
-- url     : https://prove2.me/theorems/bc69e247-33e7-4dd2-a33e-c9fffd901a5c
-- title:
--   Inverse of a PL homeomorphism is a PL homeomorphism
-- statement:
--   Let $K_1$ and $K_2$ be Euclidean complexes in $\mathbb{R}^n$ and $\mathbb{R}^m$, respectively. If $f : |K_1| \to |K_2|$ is a piecewise-linear homeomorphism, then its inverse $f^{-1} : |K_2| \to |K_1|$ is also a piecewise-linear homeomorphism.
-- source:
--   E. E. Moise, Geometric Topology in Dimensions 2 and 3, Springer GTM 47, 1977, Chapter 2, pp. 14–16.

import Mathlib.Analysis.InnerProductSpace.PiL2
import Definitions.Def_Moise_EuclideanComplex

namespace Moise

theorem isPLHomeomorph_symm {n m : ℕ}
    (K₁ : EuclideanComplex n) (K₂ : EuclideanComplex m)
    (f : K₁.polyhedron ≃ₜ K₂.polyhedron)
    (hf : IsPLHomeomorph K₁ K₂ f) :
    IsPLHomeomorph K₂ K₁ f.symm := by sorry

end Moise
