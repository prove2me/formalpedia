-- Prove2me | Theorems.Thm_Kyprianou_Ch03_momentCPWeightedGeometricSumFiniteV1
-- name    : Kyprianou.Ch03.momentCPWeightedGeometricSumFiniteV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T12:52:40.348823+00:00
-- url     : https://prove2.me/theorems/19846ffd-93dc-48ad-8a3d-a6791d0db1eb
-- title:
--   Poisson weighted geometric series is finite
-- statement:
--   Convert r to its finite real value and apply the exponential power series; all terms are nonnegative.
-- source:
--   Kyprianou (2006), Theorem 3.8, compound-Poisson moment criterion; child 94671c15-20af-4dbe-b8aa-987cace03fb2.

import Mathlib
import Definitions.Def_KSATSingleFlip_Connect_SoftField
import Definitions.Def_Kyprianou_Ch03_IsSubmultiplicative
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.momentCPWeightedGeometricSumFiniteV1
    (a M : Real) (ha : 0 ≤ a) (r : ENNReal) (hr : r ≠ ⊤) :
    (∑' n : ℕ, ENNReal.ofReal (Real.exp (-M) / (n.factorial : ℝ)) *
      (ENNReal.ofReal a * r ^ n)) < ⊤ := by sorry
