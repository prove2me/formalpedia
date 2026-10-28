-- Prove2me | Theorems.Thm_MarkovProcess_PiContinuousMap_coordinateC0Subalgebra_separatesPoints
-- name    : MarkovProcess.PiContinuousMap.coordinateC0Subalgebra_separatesPoints
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T18:12:19.308129+00:00
-- url     : https://prove2.me/theorems/983c971e-a3a4-4e27-ace7-f053392030be
-- title:
--   C0 coordinate subalgebra separates product points
-- statement:
--   The coordinate-generated C0 subalgebra separates distinct product points over any locally compact T3 space.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/FiniteTime/FiniteProductStoneWeierstrass.lean#L81-L104

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
open Topology MarkovProcess.PiContinuousMap
open scoped ZeroAtInfty
variable {I α : Type*} [TopologicalSpace α]

theorem MarkovProcess.PiContinuousMap.coordinateC0Subalgebra_separatesPoints
    [T3Space α] [LocallyCompactSpace α] :
    (coordinateC0Subalgebra (I := I) (α := α)).SeparatesPoints := by sorry
