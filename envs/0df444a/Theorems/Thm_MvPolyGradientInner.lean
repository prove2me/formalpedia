-- Prove2me | Theorems.Thm_MvPolyGradientInner
-- name    : MvPolyGradientInner
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T15:55:46.218887+00:00
-- url     : https://prove2.me/theorems/a29ef041-87f1-48d1-b255-6b37b1723265
-- title:
--   Mv Poly Gradient Inner: Mv Poly Gradient Inner
-- statement:
--   Pairing the gradient of a polynomial function against a vector, in partial
--   derivative coordinates, in both the inner-product and the linear-form form.
--
--   Source: https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/MvPolyGradientInner.lean#L10-L27
-- source:
--   https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/MvPolyGradientInner.lean#L10-L27

module
public import Definitions.Def_PHarmonicPoly_MvPolyGradient
public import Definitions.Def_PHarmonicPoly_MvPolyGradientInner
public import Theorems.Thm_MvPolyGradient

set_option autoImplicit false
@[expose] public section
public section
open MvPolynomial

theorem MvPolyGradientInner {n : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (y z : EuclideanSpace ℝ (Fin n)) :
    (inner ℝ (gradient (fun q : EuclideanSpace ℝ (Fin n) =>
          MvPolynomial.eval (fun i => q i) P) y) z : ℝ)
        = ∑ i, MvPolynomial.eval (fun j => y j) (pderiv i P) * z i
      ∧ (∑ i, (MvPolynomial.eval (fun j => y j) (pderiv i P)) •
          (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) z
        = (inner ℝ (gradient (fun q : EuclideanSpace ℝ (Fin n) =>
            MvPolynomial.eval (fun i => q i) P) y) z : ℝ) := by sorry
