-- Prove2me | Theorems.Thm_MarkovProcess_Kernel_map_denseRestriction_injective
-- name    : MarkovProcess.Kernel.map_denseRestriction_injective
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T13:46:39.691346+00:00
-- url     : https://prove2.me/theorems/15746bd4-3596-4aa9-9dee-60ce4d66f199
-- title:
--   A kernel on continuous-path space is determined by its pushforward to the fixed dense time carrier
-- statement:
--   A kernel on continuous-path space is determined by its pushforward to the fixed dense time
--   carrier.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Path/KernelIdentification.lean#L47-L63

import Definitions.Def_MarkovProcess_Continuity_DenseTimeContinuousExtension
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
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Identifying continuous-path kernels from dense-time restrictions

Restriction to the fixed dense time carrier is injective on kernels whose target is continuous-path
space.  A measurable left inverse is obtained from the total continuous-extension map.  This is a
deterministic property of continuous paths; it makes no stochastic-process, Markov, or regularity
claim.
-/

open MeasureTheory ProbabilityTheory


noncomputable section

variable {alpha beta : Type*} [TopologicalSpace alpha] [T2Space alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [MeasurableSpace beta]

variable [StandardBorelSpace (ContinuousPath alpha)]
  [MeasurableSpace.CountablySeparated (DenseTime → alpha)]

theorem MarkovProcess.Kernel.map_denseRestriction_injective :
    Function.Injective
      (fun kappa : Kernel beta (ContinuousPath alpha) ↦
        kappa.map ContinuousPath.denseRestriction) := by sorry
