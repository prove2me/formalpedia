-- Prove2me | Theorems.Thm_GreatCircleTrigPoly
-- name    : GreatCircleTrigPoly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:27:37.420359+00:00
-- url     : https://prove2.me/theorems/409fd262-4c24-49f2-8106-2d42da3fcec9
-- title:
--   Great Circle Trig Poly: Great Circle Trig Poly
-- statement:
--   Restricting a polynomial of total degree at most `m` to a circle
--   `t ↦ cos t • A + sin t • B` gives a real trigonometric polynomial of degree at
--   most `m`. This is what lets `DeficitBound` and `BernsteinSzego` be applied.
--
--   Source: https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/GreatCircleTrigPoly.lean#L12-L93
-- source:
--   https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/GreatCircleTrigPoly.lean#L12-L93

module
public import Definitions.Def_PHarmonicPoly_TrigPolyMul
public import Definitions.Def_PHarmonicPoly_TrigPolyLinComb
public import Definitions.Def_PHarmonicPoly_GreatCircleTrigPoly
public import Theorems.Thm_TrigPolyLinComb
public import Theorems.Thm_TrigPolyMul

set_option autoImplicit false
@[expose] public section
public section
open MvPolynomial

theorem GreatCircleTrigPoly {n m : ℕ} {P : MvPolynomial (Fin n) ℝ}
    (hdeg : P.totalDegree ≤ m) (A B : EuclideanSpace ℝ (Fin n)) :
    TrigPolyLe m (fun t => MvPolynomial.eval
      (fun i => (Real.cos t • A + Real.sin t • B : EuclideanSpace ℝ (Fin n)) i) P) := by sorry
