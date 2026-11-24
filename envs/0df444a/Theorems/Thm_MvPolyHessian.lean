-- Prove2me | Theorems.Thm_MvPolyHessian
-- name    : MvPolyHessian
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T15:55:53.7165+00:00
-- url     : https://prove2.me/theorems/32903ea0-ff66-49c1-98d0-47bc3ea8e475
-- title:
--   Mv Poly Hessian: Mv Poly Hessian
-- statement:
--   The second derivative of a polynomial function on `EuclideanSpace ℝ (Fin n)`,
--   as a bilinear form, is given by the matrix of second partial derivatives.
--
--   Source: https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/MvPolyHessian.lean#L11-L52
-- source:
--   https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/MvPolyHessian.lean#L11-L52

module
public import Definitions.Def_PHarmonicPoly_MvPolyGradient
public import Definitions.Def_PHarmonicPoly_MvPolyFDerivEuclidean
public import Definitions.Def_PHarmonicPoly_MvPolyHessian
public import Theorems.Thm_MvPolyFDerivEuclidean
public import Theorems.Thm_MvPolyGradient

set_option autoImplicit false
@[expose] public section
public section
open MvPolynomial

theorem MvPolyHessian {n : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (x v w : EuclideanSpace ℝ (Fin n)) :
    iteratedFDeriv ℝ 2
        (fun y : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => y i) P) x ![v, w]
      = ∑ i, ∑ j, v i * w j * MvPolynomial.eval (fun k => x k) (pderiv i (pderiv j P)) := by sorry
