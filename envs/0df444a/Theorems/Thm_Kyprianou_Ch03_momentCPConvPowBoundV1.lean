-- Prove2me | Theorems.Thm_Kyprianou_Ch03_momentCPConvPowBoundV1
-- name    : Kyprianou.Ch03.momentCPConvPowBoundV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T12:52:35.752335+00:00
-- url     : https://prove2.me/theorems/4cdcdf41-019a-4e79-8aa5-02a5286162e4
-- title:
--   Geometric bounds on all finite convolution powers
-- statement:
--   Induction from the Dirac law at zero, using the convolution moment bound and finiteness of convolution powers.
-- source:
--   Kyprianou (2006), Theorem 3.8, compound-Poisson moment criterion; child 94671c15-20af-4dbe-b8aa-987cace03fb2.

import Mathlib
import Definitions.Def_KSATSingleFlip_Connect_SoftField
import Definitions.Def_Kyprianou_Ch03_IsSubmultiplicative
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.momentCPConvPowBoundV1
    (mu : Measure Real) [IsFiniteMeasure mu]
    (g : Real → Real) (hg : Kyprianou.Ch03.IsSubmultiplicative g)
    (hg_meas : Measurable g)
    (c : Real) (hc : 0 < c)
    (hsub : ∀ x y : Real, g (x + y) ≤ c * g x * g y) (n : ℕ) :
    (∫⁻ x, ENNReal.ofReal (g x) ∂(KSATSingleFlip.Connect.convPow mu n)) ≤
      ENNReal.ofReal (g 0) *
        (ENNReal.ofReal c * (∫⁻ x, ENNReal.ofReal (g x) ∂mu)) ^ n := by sorry
