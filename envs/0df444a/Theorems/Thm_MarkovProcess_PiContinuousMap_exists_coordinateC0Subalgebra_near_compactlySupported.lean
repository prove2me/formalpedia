-- Prove2me | Theorems.Thm_MarkovProcess_PiContinuousMap_exists_coordinateC0Subalgebra_near_compactlySupported
-- name    : MarkovProcess.PiContinuousMap.exists_coordinateC0Subalgebra_near_compactlySupported
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T13:59:45.105191+00:00
-- url     : https://prove2.me/theorems/a3c9cebd-2ea0-4c2e-a02e-8bf44f074836
-- title:
--   Uniform coordinate-algebra approximation of compact tests
-- statement:
--   A compactly supported continuous function on a finite product can be approximated uniformly on
--   the whole product by the coordinate `C₀` algebra.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/FiniteTime/FiniteProductCompactSupportApproximation.lean#L64-L124

import Definitions.Def_MarkovProcess_FiniteTime_FiniteProductStoneWeierstrass
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.UrysohnsLemma
open MarkovProcess MarkovProcess.PiContinuousMap
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Compactly supported approximation on a finite product

This file upgrades compact-set Stone--Weierstrass approximation to a uniform approximation on the
whole product.  The key device is a product of one-coordinate compactly supported cutoffs.  Each
coordinate cutoff is one on the corresponding projection of the target's compact support.
-/

open Topology
open scoped CompactlySupported ZeroAtInfty


variable {I α : Type*} [Fintype I] [TopologicalSpace α]

theorem MarkovProcess.PiContinuousMap.exists_coordinateC0Subalgebra_near_compactlySupported
    [T3Space α] [LocallyCompactSpace α]
    (f : C_c(I → α, ℝ)) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ h ∈ coordinateC0Subalgebra (I := I) (α := α),
      ∀ x, ‖h x - f x‖ < epsilon := by sorry
