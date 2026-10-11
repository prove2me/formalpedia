-- Prove2me | Theorems.Thm_HunterPDE_Sobolev_sobolevNorm_sub_triangle
-- name    : HunterPDE.Sobolev.sobolevNorm_sub_triangle
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-10T22:17:46.761684+00:00
-- url     : https://prove2.me/theorems/d5dad274-f36c-46d7-b67f-50291c703047
-- title:
--   Triangle inequality for distances in the weak-derivative Sobolev norm
-- statement:
--   Let $\Omega\subseteq\mathbb R^n$ be open, $k\ge0$, and $1\le p<\infty$. For three functions $f,g,h\in W^{k,p}(\Omega)$, the norm of Definition 3.23 satisfies
--
--   $$\|f-h\|_{W^{k,p}(\Omega)}\le\|f-g\|_{W^{k,p}(\Omega)}+\|g-h\|_{W^{k,p}(\Omega)}.$$
--
--   This is the metric triangle inequality used to combine the two density steps in Hunter's Theorem 3.24, generalized to any open domain. Since the definition uses arbitrarily chosen weak derivatives, its proof must justify their almost-everywhere uniqueness and linearity, then apply the $L^p$ and finite-dimensional Minkowski inequalities. No smoothness is assumed of the three functions.
-- source:
--   John K. Hunter, Notes on Partial Differential Equations, revised 6/18/2014, https://www.math.ucdavis.edu/~hunter/pdes/pde_notes.pdf, printed pp. 58–60, Definition 3.23 and proof of Theorem 3.24.

import Definitions.Def_HunterPDE_Sobolev_SobolevSpace

open MeasureTheory
open HunterPDE.Sobolev

theorem HunterPDE.Sobolev.sobolevNorm_sub_triangle {n k : ℕ}
    {p : ENNReal} (hp : 1 ≤ p) (hptop : p ≠ ⊤)
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω)
    (f g h : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : MemW k p Ω f) (hg : MemW k p Ω g) (hh : MemW k p Ω h) :
    sobolevNorm k p Ω (f - h) ≤
      sobolevNorm k p Ω (f - g) + sobolevNorm k p Ω (g - h) := by sorry
