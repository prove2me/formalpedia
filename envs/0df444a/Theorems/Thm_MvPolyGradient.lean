-- Prove2me | Theorems.Thm_MvPolyGradient
-- name    : MvPolyGradient
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T15:13:58.857985+00:00
-- url     : https://prove2.me/theorems/76023923-a7ef-417b-bdd9-9e75e6642602
-- title:
--   Mv Poly Gradient: Mv Poly Gradient
-- statement:
--   The gradient of a polynomial function on `EuclideanSpace ℝ (Fin n)` is the
--   vector of its partial derivatives.
--
--   Source: https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/MvPolyGradient.lean#L10-L28
-- source:
--   https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/MvPolyGradient.lean#L10-L28

module
public import Definitions.Def_PHarmonicPoly_MvPolyFDeriv
public import Definitions.Def_PHarmonicPoly_MvPolyGradient
public import Theorems.Thm_MvPolyFDeriv

set_option autoImplicit false
@[expose] public section
public section
open MvPolynomial ContinuousLinearMap InnerProductSpace

theorem MvPolyGradient {n : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    gradient (fun y : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => y i) P) x
      = WithLp.toLp 2 (fun i => MvPolynomial.eval (fun j => x j) (pderiv i P)) := by sorry
