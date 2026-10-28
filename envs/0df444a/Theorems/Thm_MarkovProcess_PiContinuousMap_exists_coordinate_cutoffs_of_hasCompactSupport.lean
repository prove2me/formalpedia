-- Prove2me | Theorems.Thm_MarkovProcess_PiContinuousMap_exists_coordinate_cutoffs_of_hasCompactSupport
-- name    : MarkovProcess.PiContinuousMap.exists_coordinate_cutoffs_of_hasCompactSupport
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T18:21:20.317714+00:00
-- url     : https://prove2.me/theorems/bf4a4d44-e84d-47a6-b648-f50037d2313e
-- title:
--   Coordinatewise C0 cutoffs adapted to compact support on a finite product
-- statement:
--   A compactly supported continuous function on a finite product admits coordinatewise C0 cutoffs whose product equals one on the original topological support and vanishes outside a compact product box.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/FiniteTime/FiniteProductCompactSupportApproximation.lean#L25-L64

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
open scoped CompactlySupported ZeroAtInfty
variable {I α : Type*} [Fintype I] [TopologicalSpace α]

theorem MarkovProcess.PiContinuousMap.exists_coordinate_cutoffs_of_hasCompactSupport
    [T3Space α] [LocallyCompactSpace α] (f : C_c(I → α, ℝ)) :
    ∃ (φ : I → C₀(α, ℝ)) (B : Set (I → α)),
      IsCompact B ∧
      (∀ i x, 0 ≤ φ i x ∧ φ i x ≤ 1) ∧
      Set.EqOn (∏ i, coordinate i ((φ i : C₀(α, ℝ)) : C(α, ℝ))) 1 (tsupport f) ∧
      tsupport f ⊆ B ∧
      Set.EqOn (∏ i, coordinate i ((φ i : C₀(α, ℝ)) : C(α, ℝ))) 0 Bᶜ := by sorry
