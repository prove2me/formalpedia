-- Prove2me | Theorems.Thm_MarkovProcess_PiContinuousMap_exists_coordinateSubalgebra_near
-- name    : MarkovProcess.PiContinuousMap.exists_coordinateSubalgebra_near
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T18:21:20.958736+00:00
-- url     : https://prove2.me/theorems/d523ae23-98a4-453d-b431-477dfe02f2d7
-- title:
--   Uniform approximation on compact finite products by coordinate algebra
-- statement:
--   The continuous real-valued functions on a compact finite product can be approximated in sup norm by finite algebraic combinations of functions depending on one coordinate.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/FiniteTime/FiniteProductStoneWeierstrass.lean#L124-L131

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.UrysohnsLemma
import Definitions.Def_MarkovProcess_CoordinateProductAlgebras
import Theorems.Thm_MarkovProcess_PiContinuousMap_coordinateSubalgebra_separatesPoints
open Topology MarkovProcess.PiContinuousMap
open scoped ZeroAtInfty
variable {I α : Type*} [TopologicalSpace α]

theorem MarkovProcess.PiContinuousMap.exists_coordinateSubalgebra_near
    [Fintype I] [T35Space α] [CompactSpace α]
    (f : C(I → α, ℝ)) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ g : coordinateSubalgebra (I := I) (α := α),
      ‖(g : C(I → α, ℝ)) - f‖ < epsilon := by sorry
