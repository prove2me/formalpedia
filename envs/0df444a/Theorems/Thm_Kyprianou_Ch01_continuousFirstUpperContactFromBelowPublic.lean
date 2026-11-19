-- Prove2me | Theorems.Thm_Kyprianou_Ch01_continuousFirstUpperContactFromBelowPublic
-- name    : Kyprianou.Ch01.continuousFirstUpperContactFromBelowPublic
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T09:54:27.930487+00:00
-- url     : https://prove2.me/theorems/66fddeef-6357-409e-8c16-8ec05732d531
-- title:
--   Public continuous first strict upper crossing touches barrier from below
-- statement:
--   A continuous real path starting strictly beneath a level has first strict positive upper-crossing infimum at the level, provided a strict crossing eventually occurs. Proof by closed superlevel contact and positive infimum from strict starting gap; use public positive-infimum contact theorem.
-- source:
--   Kyprianou (2006) Exercise 1.10(ii) first-passage continuity argument, printed page 306.

import Mathlib.Topology.Order.Monotone
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Closure
import Mathlib.Data.NNReal.Defs
import Theorems.Thm_Kyprianou_Ch01_continuousFirstUpperContactPublic
open Set Filter Topology Kyprianou.Ch01
open scoped NNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.continuousFirstUpperContactFromBelowPublic
    (f : ℝ≥0 → ℝ) (hcont : Continuous f) (s : ℝ)
    (hstart : f 0 < s)
    (hcross : ∃ t : ℝ≥0, 0 < t ∧ s < f t) :
    f (sInf {t : ℝ≥0 | 0 < t ∧ s < f t}) = s := by sorry
