-- Prove2me | Theorems.Thm_MarkovProcess_Kernel_IsSupportedOnContinuousPaths_map_denseRestriction
-- name    : MarkovProcess.Kernel.IsSupportedOnContinuousPaths.map_denseRestriction
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T13:46:31.697633+00:00
-- url     : https://prove2.me/theorems/6258bb40-13a5-4a07-beeb-b8dbde9fecdf
-- title:
--   On the continuous restriction range, extension followed by restriction is the identity
-- statement:
--   On the continuous restriction range, extension followed by restriction is the identity.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Continuity/DenseTimeContinuousLaw.lean#L74-L91

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
open MarkovProcess MarkovProcess.Kernel
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Transporting dense-time laws to continuous paths

This file transports a kernel on dense-time trajectories to ordinary continuous paths under an
explicit support-on-the-continuous-range hypothesis. It does not prove that support hypothesis.
-/

open MeasureTheory ProbabilityTheory Set


noncomputable section


variable {β alpha : Type*} [MeasurableSpace β] [TopologicalSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [T2Space alpha]

variable [StandardBorelSpace (ContinuousPath alpha)]
  [MeasurableSpace.CountablySeparated (DenseTime → alpha)]

theorem MarkovProcess.Kernel.IsSupportedOnContinuousPaths.map_denseRestriction
    (κ : Kernel β (DenseTime → alpha)) (hκ : IsSupportedOnContinuousPaths κ)
    (default : ContinuousPath alpha) :
    (toContinuousPathKernel κ default).map ContinuousPath.denseRestriction = κ := by sorry
