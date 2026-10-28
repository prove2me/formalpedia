-- Prove2me | Theorems.Thm_MarkovProcess_PiContinuousMap_coordinateSubalgebra_topologicalClosure_eq_top
-- name    : MarkovProcess.PiContinuousMap.coordinateSubalgebra_topologicalClosure_eq_top
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T18:21:24.960223+00:00
-- url     : https://prove2.me/theorems/b309d0af-acd2-4363-98f1-399460f76ba4
-- title:
--   Stone–Weierstrass closure of coordinate-generated product algebra
-- statement:
--   For a compact T3.5 state space and finitely many coordinates, the coordinate-generated continuous-function subalgebra has topological closure equal to the entire continuous-function algebra.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/FiniteTime/FiniteProductStoneWeierstrass.lean#L117-L123

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

theorem MarkovProcess.PiContinuousMap.coordinateSubalgebra_topologicalClosure_eq_top
    [Fintype I] [T35Space α] [CompactSpace α] :
    (coordinateSubalgebra (I := I) (α := α)).topologicalClosure = ⊤ := by sorry
