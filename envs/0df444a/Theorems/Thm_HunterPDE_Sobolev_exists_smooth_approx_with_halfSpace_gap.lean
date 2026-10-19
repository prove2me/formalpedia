-- Prove2me | Theorems.Thm_HunterPDE_Sobolev_exists_smooth_approx_with_halfSpace_gap
-- name    : HunterPDE.Sobolev.exists_smooth_approx_with_halfSpace_gap
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-16T21:03:48.67216+00:00
-- url     : https://prove2.me/theorems/1074e39d-5302-444a-8165-13dd9a84bd1f
-- title:
--   Smooth Sobolev approximation with a positive half-space support gap
-- statement:
--   Let $F\in W^{k,p}(\mathbb R^{m+1})$, with $k\ge0$ and $1\le p<\infty$, vanish almost everywhere outside the closed upper half-space. For every $\varepsilon>0$, there are a globally smooth $g\in W^{k,p}(\mathbb R^{m+1})$ and a number $\delta>0$ such that
--
--   $$\operatorname{supp}g\subseteq\{x:x_{m+1}\ge\delta\},\qquad \|F-g\|_{W^{k,p}(\mathbb R^{m+1})}<\varepsilon.$$
--
--   No compact support is required. This isolates inward translation and mollification from the separate large-radius cutoff step, and provides a uniform positive distance from the boundary.
-- source:
--   J. K. Hunter, Notes on Partial Differential Equations, revised 6/18/2014, https://www.math.ucdavis.edu/~hunter/pdes/ch3.pdf, Theorem 3.44, printed pp. 72–73. Support-preserving translation and mollification argument on printed p. 73; generalization to arbitrary finite Sobolev order, with whole-space cutoff as in Theorem 3.24. This interface isolates the translation and mollification stage before taking a compact cutoff.

import Definitions.Def_HunterPDE_Compactness_Sobolev
import Definitions.Def_HunterPDE_Compactness_HalfSpace
import Definitions.Def_HunterPDE_Sobolev_SobolevSpace
open MeasureTheory HunterPDE.Compactness
open scoped ENNReal NNReal
set_option autoImplicit false

theorem HunterPDE.Sobolev.exists_smooth_approx_with_halfSpace_gap {m k : ℕ} {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (F : EuclideanSpace ℝ (Fin (m + 1)) → ℝ)
    (hF : HunterPDE.Sobolev.MemW k p Set.univ F)
    (hsupport : ∀ᵐ x ∂volume, x ∉ closedUpperHalfSpace m → F x = 0)
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ (g : EuclideanSpace ℝ (Fin (m + 1)) → ℝ) (δ : ℝ),
      0 < δ ∧ ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧
      HunterPDE.Sobolev.MemW k p Set.univ g ∧
      tsupport g ⊆ {x | δ ≤ x (Fin.last m)} ∧
      HunterPDE.Sobolev.sobolevNorm k p Set.univ (F - g) < ε := by sorry
