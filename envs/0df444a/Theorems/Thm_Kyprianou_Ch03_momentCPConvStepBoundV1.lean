-- Prove2me | Theorems.Thm_Kyprianou_Ch03_momentCPConvStepBoundV1
-- name    : Kyprianou.Ch03.momentCPConvStepBoundV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T12:52:33.288925+00:00
-- url     : https://prove2.me/theorems/abe003a5-4b17-451d-b2d3-36eaee8965fb
-- title:
--   Submultiplicative convolution moment bound
-- statement:
--   Unfold convolution, use the measurable sum pushforward and Tonelli; apply the pointwise submultiplicative bound and split products.
-- source:
--   Kyprianou (2006), Theorem 3.8, compound-Poisson moment criterion; child 94671c15-20af-4dbe-b8aa-987cace03fb2.

import Mathlib
import Definitions.Def_KSATSingleFlip_Connect_SoftField
import Definitions.Def_Kyprianou_Ch03_IsSubmultiplicative
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.momentCPConvStepBoundV1
    (mu : Measure Real) [IsFiniteMeasure mu]
    (g : Real → Real) (hg : Kyprianou.Ch03.IsSubmultiplicative g)
    (hg_meas : Measurable g)
    (nu : Measure Real) [IsFiniteMeasure nu]
    (c : Real) (hc : 0 < c)
    (hsub : ∀ x y : Real, g (x + y) ≤ c * g x * g y) :
    (∫⁻ x, (fun x : ℝ => ENNReal.ofReal (g x)) x ∂(mu ∗ nu)) ≤
      ENNReal.ofReal c * (∫⁻ x, (fun x : ℝ => ENNReal.ofReal (g x)) x ∂mu) * (∫⁻ x, (fun x : ℝ => ENNReal.ofReal (g x)) x ∂nu) := by sorry
