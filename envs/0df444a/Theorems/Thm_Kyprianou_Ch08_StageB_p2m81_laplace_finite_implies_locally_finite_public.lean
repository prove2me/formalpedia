-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m81_laplace_finite_implies_locally_finite_public
-- name    : Kyprianou.Ch08.StageB.p2m81_laplace_finite_implies_locally_finite_public
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T04:11:27.393838+00:00
-- url     : https://prove2.me/theorems/6eda0554-eefb-44f2-983e-9499c089d896
-- title:
--   Finite unit Laplace implies locally finite distribution
-- statement:
--   If the Laplace transform at rate 1 is finite, the measure is finite on every Iic x for x>=0, via the exp bound 1 <= exp(x)*exp(-y) on Iic x and monotonicity of the restricted integral.
-- source:
--   Decomposition of Kyprianou.Ch08.StageB.p2m81_geometric_renewal_from_gap (1683b347-a85a-4b0e-b47b-61a14cca75e1): source-faithful public child for code-budget split (167 lines/6157 tokens exceed 100/2500 caps). Local finiteness of the renewal measure from finiteness of its Laplace at s=1.

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.p2m81_laplace_finite_implies_locally_finite_public
    (ν : Measure ℝ)
    (hfin1 : (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-(1:ℝ) * y)) ∂ν) < ⊤) :
    ∀ x : ℝ, 0 ≤ x → ν (Iic x) < ⊤ := by sorry
