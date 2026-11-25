-- Prove2me | Theorems.Thm_GradientEuler
-- name    : GradientEuler
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:36:07.49666+00:00
-- url     : https://prove2.me/theorems/0c9c3a3d-37bd-477f-ae4a-b471e3e8f19b
-- title:
--   Gradient Euler: Gradient Euler
-- statement:
--   Euler's identity transported through the bridge: the radial first and second
--   derivatives of a homogeneous polynomial function.
--
--   Source: https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/GradientEuler.lean#L11-L44
-- source:
--   https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/GradientEuler.lean#L11-L44

module
public import Definitions.Def_PHarmonicPoly_MvPolyHessian
public import Definitions.Def_PHarmonicPoly_MvPolyGradientInner
public import Definitions.Def_PHarmonicPoly_GradientEuler
public import Theorems.Thm_MvPolyGradientInner
public import Theorems.Thm_MvPolyHessian

set_option autoImplicit false
@[expose] public section
public section
open MvPolynomial

theorem GradientEuler {n m : ℕ} (hm : 1 ≤ m) {P : MvPolynomial (Fin n) ℝ}
    (hhom : P.IsHomogeneous m) (x w : EuclideanSpace ℝ (Fin n)) :
    inner ℝ (gradient (fun y : EuclideanSpace ℝ (Fin n) =>
          MvPolynomial.eval (fun i => y i) P) x) x
        = (m : ℝ) * MvPolynomial.eval (fun i => x i) P
      ∧ iteratedFDeriv ℝ 2
          (fun y : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => y i) P) x ![x, w]
        = ((m : ℝ) - 1) * inner ℝ (gradient (fun y : EuclideanSpace ℝ (Fin n) =>
            MvPolynomial.eval (fun i => y i) P) x) w := by sorry
