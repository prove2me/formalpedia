-- Prove2me | Theorems.Thm_MarkovProcess_PiContinuousMap_exists_coordinateC0Subalgebra_near_on_isCompact
-- name    : MarkovProcess.PiContinuousMap.exists_coordinateC0Subalgebra_near_on_isCompact
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T18:21:18.104116+00:00
-- url     : https://prove2.me/theorems/bb0e55fe-a3f5-4252-a42f-255d4aeed823
-- title:
--   Uniform C0 coordinate-algebra approximation on a compact set
-- statement:
--   On every compact subset of a product of locally compact T3 spaces, algebraic coordinate C0 combinations uniformly approximate any continuous real-valued function.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/FiniteTime/FiniteProductStoneWeierstrass.lean#L106-L115

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
import Theorems.Thm_MarkovProcess_PiContinuousMap_coordinateC0Subalgebra_separatesPoints
open Topology MarkovProcess.PiContinuousMap
open scoped ZeroAtInfty
variable {I α : Type*} [TopologicalSpace α]

theorem MarkovProcess.PiContinuousMap.exists_coordinateC0Subalgebra_near_on_isCompact
    [T3Space α] [LocallyCompactSpace α]
    (f : C(I → α, ℝ)) {K : Set (I → α)} (hK : IsCompact K)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ g ∈ coordinateC0Subalgebra (I := I) (α := α),
      ∀ x ∈ K, ‖g x - f x‖ < epsilon := by sorry
