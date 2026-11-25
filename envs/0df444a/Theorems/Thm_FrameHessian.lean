-- Prove2me | Theorems.Thm_FrameHessian
-- name    : FrameHessian
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:50:46.996023+00:00
-- url     : https://prove2.me/theorems/d4478833-a3e8-4463-8fdd-33a0664722a1
-- title:
--   Frame Hessian: Frame Hessian
-- statement:
--   The paper's eq:frame: the gradient and Hessian of a homogeneous polynomial
--   at a point of a great circle, in the polar frame `{e_r, e_θ}` of the plane.
--
--   Source: https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/FrameHessian.lean#L13-L100
-- source:
--   https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/FrameHessian.lean#L13-L100

module
public import Definitions.Def_PHarmonicPoly_GradientEuler
public import Definitions.Def_PHarmonicPoly_GreatCircleSecondDeriv
public import Definitions.Def_PHarmonicPoly_MvPolyFDerivEuclidean
public import Definitions.Def_PHarmonicPoly_MvPolyGradientInner
public import Definitions.Def_PHarmonicPoly_FrameHessian
public import Theorems.Thm_GradientEuler
public import Theorems.Thm_GreatCircleSecondDeriv
public import Theorems.Thm_MvPolyFDerivEuclidean
public import Theorems.Thm_MvPolyGradientInner

set_option autoImplicit false
@[expose] public section
public section
open MvPolynomial

theorem FrameHessian {n m : ℕ} (hm : 1 ≤ m) {P : MvPolynomial (Fin n) ℝ}
    (hhom : P.IsHomogeneous m) (e v : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    inner ℝ (gradient (fun y : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => y i) P)
          (Real.cos t • e + Real.sin t • v)) (Real.cos t • e + Real.sin t • v)
        = (m : ℝ) * MvPolynomial.eval
            (fun i => (Real.cos t • e + Real.sin t • v : EuclideanSpace ℝ (Fin n)) i) P
      ∧ inner ℝ (gradient (fun y : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => y i) P)
          (Real.cos t • e + Real.sin t • v)) (-Real.sin t • e + Real.cos t • v)
        = deriv (fun s : ℝ => MvPolynomial.eval
            (fun i => (Real.cos s • e + Real.sin s • v : EuclideanSpace ℝ (Fin n)) i) P) t
      ∧ iteratedFDeriv ℝ 2
          (fun y : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => y i) P)
          (Real.cos t • e + Real.sin t • v)
          ![Real.cos t • e + Real.sin t • v, Real.cos t • e + Real.sin t • v]
        = (m : ℝ) * ((m : ℝ) - 1) * MvPolynomial.eval
            (fun i => (Real.cos t • e + Real.sin t • v : EuclideanSpace ℝ (Fin n)) i) P
      ∧ iteratedFDeriv ℝ 2
          (fun y : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => y i) P)
          (Real.cos t • e + Real.sin t • v)
          ![Real.cos t • e + Real.sin t • v, -Real.sin t • e + Real.cos t • v]
        = ((m : ℝ) - 1) * deriv (fun s : ℝ => MvPolynomial.eval
            (fun i => (Real.cos s • e + Real.sin s • v : EuclideanSpace ℝ (Fin n)) i) P) t
      ∧ iteratedFDeriv ℝ 2
          (fun y : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => y i) P)
          (Real.cos t • e + Real.sin t • v)
          ![-Real.sin t • e + Real.cos t • v, -Real.sin t • e + Real.cos t • v]
        = iteratedDeriv 2 (fun s : ℝ => MvPolynomial.eval
            (fun i => (Real.cos s • e + Real.sin s • v : EuclideanSpace ℝ (Fin n)) i) P) t
          + (m : ℝ) * MvPolynomial.eval
            (fun i => (Real.cos t • e + Real.sin t • v : EuclideanSpace ℝ (Fin n)) i) P := by sorry
