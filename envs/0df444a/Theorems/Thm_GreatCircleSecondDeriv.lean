-- Prove2me | Theorems.Thm_GreatCircleSecondDeriv
-- name    : GreatCircleSecondDeriv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:35:25.217041+00:00
-- url     : https://prove2.me/theorems/e939e16e-1a7a-40f9-952f-9bf16403b690
-- title:
--   Great Circle Second Deriv: Great Circle Second Deriv
-- statement:
--   Second derivative of a polynomial function along a circle
--   `γ s = C + cos s • A + sin s • B`. Since `γ'' = -(γ - C)`, the first-order term
--   appears as `- ⟪grad u (γ t), cos t • A + sin t • B⟫`.
--
--   Source: https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/GreatCircleSecondDeriv.lean#L12-L154
-- source:
--   https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/GreatCircleSecondDeriv.lean#L12-L154

module
public import Definitions.Def_PHarmonicPoly_MvPolyHessian
public import Definitions.Def_PHarmonicPoly_MvPolyFDerivEuclidean
public import Definitions.Def_PHarmonicPoly_GreatCircleSecondDeriv
public import Theorems.Thm_MvPolyFDerivEuclidean
public import Theorems.Thm_MvPolyHessian

set_option autoImplicit false
@[expose] public section
public section
open MvPolynomial

theorem GreatCircleSecondDeriv {n : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (C A B : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    iteratedDeriv 2 (fun s : ℝ => MvPolynomial.eval
        (fun i => (C + Real.cos s • A + Real.sin s • B : EuclideanSpace ℝ (Fin n)) i) P) t
      = iteratedFDeriv ℝ 2
          (fun y : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => y i) P)
          (C + Real.cos t • A + Real.sin t • B)
          ![-Real.sin t • A + Real.cos t • B, -Real.sin t • A + Real.cos t • B]
        - inner ℝ
            (gradient (fun y : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => y i) P)
              (C + Real.cos t • A + Real.sin t • B))
            (Real.cos t • A + Real.sin t • B) := by sorry
