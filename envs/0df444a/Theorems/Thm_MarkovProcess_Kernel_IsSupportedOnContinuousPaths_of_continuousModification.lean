-- Prove2me | Theorems.Thm_MarkovProcess_Kernel_IsSupportedOnContinuousPaths_of_continuousModification
-- name    : MarkovProcess.Kernel.IsSupportedOnContinuousPaths.of_continuousModification
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T13:46:43.523895+00:00
-- url     : https://prove2.me/theorems/0974d23c-09bd-4ef4-a831-11c18452dd47
-- title:
--   Continuous modifications imply support on continuous paths
-- statement:
--   A continuous-time modification of every coordinate law implies that the original dense-time
--   law is almost surely the restriction of a continuous path. The modification may depend on the
--   kernel parameter `b`; no measurable choice of modifications in `b` is required for this
--   pointwise support conclusion.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Continuity/DenseTimeContinuousSupport.lean#L32-L53

import Definitions.Def_MarkovProcess_Continuity_DenseTimeContinuousExtension
import Definitions.Def_MarkovProcess_Continuity_DenseTimeContinuousLaw
import Definitions.Def_MarkovProcess_Path_Basic_SourceClosedV3
import Definitions.Def_MarkovProcess_Time_CountableDenseTime
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Encodable
import Mathlib.Logic.Denumerable
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Process.Filtration
import Mathlib.Topology.CompactOpen
open MarkovProcess
open MarkovProcess.Kernel
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Continuous support from a continuous modification

This file turns a continuous-time modification of the coordinate process of a dense-time law
into almost-sure support on restrictions of continuous paths. The only measure-theoretic step is
the simultaneous choice of all dense-time modification identities, which is valid because
`DenseTime` is countable.

The continuous modification itself is not constructed here: it is the Kolmogorov--Chentsov
argument of `Continuity/GlobalDyadicFloorModification.lean`, applied to dense-time trajectory
kernels in `Continuity/KolmogorovDenseTimeContinuousSupport.lean`.
-/

open MeasureTheory ProbabilityTheory Set


noncomputable section


variable {beta alpha : Type*} [MeasurableSpace beta] [TopologicalSpace alpha]
  [MeasurableSpace alpha]

theorem MarkovProcess.Kernel.IsSupportedOnContinuousPaths.of_continuousModification
    (kappa : Kernel beta (DenseTime → alpha))
    (hmod : ∀ b, ∃ Y : NNReal → (DenseTime → alpha) → alpha,
      (∀ omega, Continuous (fun t ↦ Y t omega)) ∧
        ∀ q, (fun omega : DenseTime → alpha ↦ omega q) =ᵐ[kappa b]
          Y (DenseTime.castOrderEmbedding q)) :
    IsSupportedOnContinuousPaths kappa := by sorry
