-- Prove2me | Theorems.Thm_Moise_isPLMap_comp
-- name    : Moise.isPLMap_comp
-- status  : Open
-- author  : @wojtek_politarczyk
-- created : 2026-11-24T17:40:44.286736+00:00
-- url     : https://prove2.me/theorems/2092ffa8-7078-42f0-9d52-f1368ce0dd34
-- title:
--   Composition of piecewise-linear maps is piecewise linear
-- statement:
--   Let $K_1, K_2, K_3$ be Euclidean complexes in $\mathbb{R}^n, \mathbb{R}^m, \mathbb{R}^k$, respectively. If $f : |K_1| \to |K_2|$ and $g : |K_2| \to |K_3|$ are piecewise-linear maps, then their composition $g \circ f : |K_1| \to |K_3|$ is a piecewise-linear map.
-- source:
--   E. E. Moise, Geometric Topology in Dimensions 2 and 3, Springer GTM 47, 1977, Chapter 2, pp. 14–16.

import Mathlib.Analysis.InnerProductSpace.PiL2
import Definitions.Def_Moise_EuclideanComplex

namespace Moise

theorem isPLMap_comp {n m k : ℕ}
    (K₁ : EuclideanComplex n) (K₂ : EuclideanComplex m) (K₃ : EuclideanComplex k)
    (f : K₁.polyhedron → K₂.polyhedron) (g : K₂.polyhedron → K₃.polyhedron)
    (hf : IsPLMap K₁ K₂ f) (hg : IsPLMap K₂ K₃ g) :
    IsPLMap K₁ K₃ (g ∘ f) := by sorry

end Moise
