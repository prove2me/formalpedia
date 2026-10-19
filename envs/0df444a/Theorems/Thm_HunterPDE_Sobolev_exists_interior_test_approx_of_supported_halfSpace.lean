-- Prove2me | Theorems.Thm_HunterPDE_Sobolev_exists_interior_test_approx_of_supported_halfSpace
-- name    : HunterPDE.Sobolev.exists_interior_test_approx_of_supported_halfSpace
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-16T20:51:58.895949+00:00
-- url     : https://prove2.me/theorems/bfb3bb11-743c-4547-adfc-2143a22c59b8
-- title:
--   Interior test approximation of global Sobolev functions supported in a closed half-space
-- statement:
--   Let $k\ge0$ be an integer, $1\le p<\infty$, and let $F\in W^{k,p}(\mathbb R^{m+1})$ vanish almost everywhere outside the closed upper half-space. For every $\varepsilon>0$ there is a globally smooth function $\varphi$ with compact support contained in the open upper half-space such that $\varphi\in W^{k,p}(\mathbb R^{m+1})$ and
--
--   $$\|F-\varphi\|_{W^{k,p}(\mathbb R^{m+1})}<\varepsilon.$$
--
--   The error is measured on the whole space. No trace operator occurs in the hypotheses.
-- source:
--   J. K. Hunter, Notes on Partial Differential Equations, revised 6/18/2014, https://www.math.ucdavis.edu/~hunter/pdes/ch3.pdf, Theorem 3.44, printed pp. 72–73. Support-preserving translation and mollification argument on printed p. 73; generalization to arbitrary finite Sobolev order, with whole-space cutoff as in Theorem 3.24.

import Definitions.Def_HunterPDE_Compactness_Sobolev
import Definitions.Def_HunterPDE_Compactness_HalfSpace
import Definitions.Def_HunterPDE_Sobolev_SobolevSpace
open MeasureTheory HunterPDE.Compactness
open scoped ENNReal NNReal
set_option autoImplicit false

theorem HunterPDE.Sobolev.exists_interior_test_approx_of_supported_halfSpace {m k : ℕ} {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (F : EuclideanSpace ℝ (Fin (m + 1)) → ℝ)
    (hF : HunterPDE.Sobolev.MemW k p Set.univ F)
    (hsupport : ∀ᵐ x ∂volume, x ∉ closedUpperHalfSpace m → F x = 0)
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ φ : EuclideanSpace ℝ (Fin (m + 1)) → ℝ,
      HunterPDE.Shared.IsTestFunction (upperHalfSpace m) φ ∧
      HunterPDE.Sobolev.MemW k p Set.univ φ ∧
      HunterPDE.Sobolev.sobolevNorm k p Set.univ (F - φ) < ε := by sorry
