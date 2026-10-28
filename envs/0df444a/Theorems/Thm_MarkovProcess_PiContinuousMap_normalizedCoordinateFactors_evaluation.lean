-- Prove2me | Theorems.Thm_MarkovProcess_PiContinuousMap_normalizedCoordinateFactors_evaluation
-- name    : MarkovProcess.PiContinuousMap.normalizedCoordinateFactors_evaluation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T13:47:22.588296+00:00
-- url     : https://prove2.me/theorems/c88407c4-3a07-4e09-af35-2e938db1c8d1
-- title:
--   Normalisation preserves coordinate-product evaluations
-- statement:
--   Normalization merges every factor at the same coordinate into a single optional `C₀`
--   factor and preserves pointwise evaluation.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/FiniteTime/CoordinateProductNormalization.lean#L64-L93

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
# Normalizing finite coordinate products

This file groups every factor of a `CoordinateProductTerm (Fin n) alpha` by its coordinate.
The normalized representation is a function into `Option C₀(alpha, ℝ)`: an active coordinate
contains the single product of all its original factors, while an inactive coordinate is `none`.

Using `none` is essential because `C₀(alpha, ℝ)` generally has no constant-one element.  Scalar
evaluation interprets inactivity as `1 : ℝ`, but the normalization itself never constructs a
spurious `1 : C₀(alpha, ℝ)`.  The resulting evaluation identity is suitable for backward kernel
recursions that branch only over active coordinates.

This is purely algebraic finite-product infrastructure: it involves no measure and no kernel.
-/

open scoped CompactlySupported ZeroAtInfty BigOperators


variable {n : ℕ} {alpha : Type*} [TopologicalSpace alpha]

theorem MarkovProcess.PiContinuousMap.normalizedCoordinateFactors_evaluation
    (factors : List (Fin n × C₀(alpha, ℝ))) (x : Fin n → alpha) :
    (factors.map fun p ↦ p.2 (x p.1)).prod =
      ∏ i, evalOptionalFactor (x i) (normalizedCoordinateFactors factors i) := by sorry
