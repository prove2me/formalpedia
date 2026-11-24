-- Prove2me | Theorems.Thm_MvPolyFDeriv
-- name    : MvPolyFDeriv
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T14:26:32.188799+00:00
-- url     : https://prove2.me/theorems/1b0579e8-e99c-46f6-ac7c-7942178163d9
-- title:
--   Mv Poly FDeriv: Mv Poly FDeriv
-- statement:
--   The `pderiv`-to-`fderiv` bridge: the polynomial function `v ↦ P v` on the
--   coordinate space `Fin n → ℝ` is Frechet differentiable at every point, with
--   derivative the linear form `w ↦ ∑ i, (pderiv i P)(x) * w i`.
--
--   Source: https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/MvPolyFDeriv.lean#L11-L42
-- source:
--   https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/MvPolyFDeriv.lean#L11-L42

module
public import Definitions.Def_PHarmonicPoly_Preamble
public import Definitions.Def_PHarmonicPoly_MvPolyFDeriv
set_option autoImplicit false
@[expose] public section
public section
open MvPolynomial ContinuousLinearMap

theorem MvPolyFDeriv {n : ℕ} (P : MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ) :
    HasFDerivAt (fun v : Fin n → ℝ => MvPolynomial.eval v P)
      (∑ i, (MvPolynomial.eval x (pderiv i P)) •
        (proj i : (Fin n → ℝ) →L[ℝ] ℝ)) x := by sorry
