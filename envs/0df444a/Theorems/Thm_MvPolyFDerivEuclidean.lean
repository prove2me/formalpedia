-- Prove2me | Theorems.Thm_MvPolyFDerivEuclidean
-- name    : MvPolyFDerivEuclidean
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T15:14:27.404976+00:00
-- url     : https://prove2.me/theorems/3cd05280-da4a-464e-9a40-cf750f9042b0
-- title:
--   Mv Poly FDeriv Euclidean: Mv Poly FDeriv Euclidean
-- statement:
--   The `pderiv`-to-`fderiv` bridge on `EuclideanSpace ℝ (Fin n)`: the polynomial
--   function `z ↦ Q z` is Frechet differentiable at every point `y`, with derivative
--   the continuous linear form `w ↦ ∑ i, (pderiv i Q)(y) * w i`. This is
--   `MvPolyFDeriv` transported across the isometric linear equivalence
--   `EuclideanSpace.equiv`, which is the identity on coordinates.
--
--   Source: https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/MvPolyFDerivEuclidean.lean#L13-L25
-- source:
--   https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/MvPolyFDerivEuclidean.lean#L13-L25

module
public import Definitions.Def_PHarmonicPoly_MvPolyFDeriv
public import Definitions.Def_PHarmonicPoly_MvPolyFDerivEuclidean
public import Theorems.Thm_MvPolyFDeriv

set_option autoImplicit false
@[expose] public section
public section
open MvPolynomial

theorem MvPolyFDerivEuclidean {n : ℕ} (Q : MvPolynomial (Fin n) ℝ)
    (y : EuclideanSpace ℝ (Fin n)) :
    HasFDerivAt (fun z : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => z i) Q)
      (∑ i, (MvPolynomial.eval (fun j => y j) (pderiv i Q)) •
        (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) y := by sorry
