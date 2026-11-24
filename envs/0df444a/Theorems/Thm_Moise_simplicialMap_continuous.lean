-- Prove2me | Theorems.Thm_Moise_simplicialMap_continuous
-- name    : Moise.simplicialMap_continuous
-- status  : Open
-- author  : @wojtek_politarczyk
-- created : 2026-11-24T17:29:10.942514+00:00
-- url     : https://prove2.me/theorems/7603a2ca-fcd1-4853-8ca8-cc93440c1594
-- title:
--   Continuity of simplicial maps
-- statement:
--   Let $K_1$ be a Euclidean complex in $\mathbb{R}^n$ and $K_2$ a Euclidean complex in $\mathbb{R}^m$. Every simplicial map $f : |K_1| \to |K_2|$ is continuous.
-- source:
--   E. E. Moise, Geometric Topology in Dimensions 2 and 3, Springer GTM 47, 1977, Chapter 2, pp. 12–16.

import Mathlib.Analysis.InnerProductSpace.PiL2
import Definitions.Def_Moise_EuclideanComplex

namespace Moise

theorem simplicialMap_continuous {n m : ℕ}
    (K₁ : EuclideanComplex n) (K₂ : EuclideanComplex m)
    (f : K₁.polyhedron → K₂.polyhedron)
    (hf : IsSimplicialMap K₁ K₂ f) :
    Continuous f := by sorry

end Moise
