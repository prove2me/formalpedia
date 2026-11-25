-- Prove2me | Theorems.Thm_MvPolyLaplacian
-- name    : MvPolyLaplacian
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:36:21.059393+00:00
-- url     : https://prove2.me/theorems/3f445eab-cc53-4a71-919c-7253f395804f
-- title:
--   Mv Poly Laplacian: Mv Poly Laplacian
-- statement:
--   The Laplacian of a polynomial function on `EuclideanSpace ℝ (Fin n)` is the
--   sum of its pure second partial derivatives.
--
--   Source: https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/MvPolyLaplacian.lean#L10-L27
-- source:
--   https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/MvPolyLaplacian.lean#L10-L27

module
public import Definitions.Def_PHarmonicPoly_MvPolyHessian
public import Definitions.Def_PHarmonicPoly_MvPolyLaplacian
public import Theorems.Thm_MvPolyHessian

set_option autoImplicit false
@[expose] public section
public section
open MvPolynomial

theorem MvPolyLaplacian {n : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    Laplacian.laplacian
        (fun y : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => y i) P) x
      = ∑ i, MvPolynomial.eval (fun j => x j) (pderiv i (pderiv i P)) := by sorry
