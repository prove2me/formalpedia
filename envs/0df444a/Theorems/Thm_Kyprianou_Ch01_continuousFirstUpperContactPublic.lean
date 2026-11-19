-- Prove2me | Theorems.Thm_Kyprianou_Ch01_continuousFirstUpperContactPublic
-- name    : Kyprianou.Ch01.continuousFirstUpperContactPublic
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T09:40:28.06845+00:00
-- url     : https://prove2.me/theorems/104abdfd-f9e5-4966-8bf0-8c273ff2c3e8
-- title:
--   Source-faithful public first strict upper passage continuous path contact
-- statement:
--   For a continuous real path starting no higher than a level, with a strictly positive first strict crossing time that exists, the path at that crossing infimum equals the level. It is the public version of a previously Proved deterministic result, supporting Brownian stopped exponential boundary contact in Kyprianou Exercise 1.10(ii).
-- source:
--   Kyprianou (2006), Chapter 1, Exercise 1.10(ii) worked solution, printed page 306.

import Mathlib.Topology.UniformSpace.Real
import Mathlib.Topology.Order.Monotone
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Closure
import Mathlib.Data.NNReal.Defs
open Set Filter Topology
open scoped NNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.continuousFirstUpperContactPublic
    (f : ℝ≥0 → ℝ) (hcont : Continuous f) (s : ℝ)
    (hzero : f 0 ≤ s)
    (hcross : ∃ t : ℝ≥0, 0 < t ∧ s < f t)
    (hpos : 0 < sInf {t : ℝ≥0 | 0 < t ∧ s < f t}) :
    f (sInf {t : ℝ≥0 | 0 < t ∧ s < f t}) = s := by sorry
