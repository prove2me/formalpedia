-- Prove2me | Theorems.Thm_MarkovProcess_PiContinuousMap_normalizedCoordinateFactors_evaluation_active
-- name    : MarkovProcess.PiContinuousMap.normalizedCoordinateFactors_evaluation_active
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T13:47:18.740369+00:00
-- url     : https://prove2.me/theorems/d427a23f-df0d-411c-b5da-f6f8b167de65
-- title:
--   Normalised coordinate factors reduce to active coordinates
-- statement:
--   The product of all optional normalized factors equals the product over active coordinates.
--   In particular, this holds uniformly when the active set, or the ambient `Fin n`, is empty.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/FiniteTime/CoordinateProductActiveReduction.lean#L57-L86

import Definitions.Def_MarkovProcess_FiniteTime_CoordinateProductActiveReduction
import Definitions.Def_MarkovProcess_FiniteTime_CoordinateProductNormalization
import Definitions.Def_MarkovProcess_FiniteTime_FiniteProductCoordinateNormalForm
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
# Restricting normalized coordinate products to active coordinates

This file enumerates the active coordinates of a normalized `CoordinateProductTerm`, extracts
their genuine `C₀` factors, and proves that evaluation factors through the corresponding
coordinate restriction.  The restricting function is definitionally the same path operation as
`FiniteOrderedTimes.restrictPath (activeOrderEmbedding factors)` when that finite-time API is in
scope.

If there are no active coordinates, the reduced index type is `Fin 0` and the empty scalar
product is one.  No constant-one element of `C₀` is constructed.  This is purely algebraic
finite-product infrastructure: it involves no measure and no kernel.
-/

open scoped CompactlySupported ZeroAtInfty BigOperators


variable {n : ℕ} {alpha : Type*} [TopologicalSpace alpha]

theorem MarkovProcess.PiContinuousMap.normalizedCoordinateFactors_evaluation_active
    (factors : List (Fin n × C₀(alpha, ℝ))) (x : Fin n → alpha) :
    ∏ i, evalOptionalFactor (x i) (normalizedCoordinateFactors factors i) =
      ∏ j, activeNormalizedFactor factors j (x (activeOrderEmbedding factors j)) := by sorry
