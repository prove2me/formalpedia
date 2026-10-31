-- Prove2me | Theorems.Thm_MarkovProcess_Kernel_map_denseRestriction_map_continuousExtension
-- name    : MarkovProcess.Kernel.map_denseRestriction_map_continuousExtension
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T08:32:36.676995+00:00
-- url     : https://prove2.me/theorems/2cf0c685-e5c3-44d6-bf19-ef82d1c2e384
-- title:
--   MarkovProcess: map_denseRestriction_map_continuousExtension
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Continuity_DenseTimeContinuousExtension_479df42c
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

namespace MarkovProcess
namespace Kernel

noncomputable section

variable {alpha beta : Type*} [TopologicalSpace alpha] [T2Space alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [MeasurableSpace beta]

variable [StandardBorelSpace (ContinuousPath alpha)]
  [MeasurableSpace.CountablySeparated (DenseTime → alpha)]







end
end Kernel
end MarkovProcess


open MarkovProcess
open MarkovProcess.Kernel
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



variable {alpha beta : Type*} [TopologicalSpace alpha] [T2Space alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [MeasurableSpace beta]

variable [StandardBorelSpace (ContinuousPath alpha)]
  [MeasurableSpace.CountablySeparated (DenseTime → alpha)]

open MarkovProcess.Kernel in

@[simp]

theorem MarkovProcess.Kernel.map_denseRestriction_map_continuousExtension
    (kappa : Kernel beta (ContinuousPath alpha)) (default : ContinuousPath alpha) :
    (kappa.map ContinuousPath.denseRestriction).map
        (ContinuousPath.continuousExtension default) = kappa := by sorry
