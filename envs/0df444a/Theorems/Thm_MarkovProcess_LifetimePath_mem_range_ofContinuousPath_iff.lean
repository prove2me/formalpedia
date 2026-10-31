-- Prove2me | Theorems.Thm_MarkovProcess_LifetimePath_mem_range_ofContinuousPath_iff
-- name    : MarkovProcess.LifetimePath.mem_range_ofContinuousPath_iff
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:30:23.075096+00:00
-- url     : https://prove2.me/theorems/d46b81f0-5d62-4321-82c3-82648b2ab715
-- title:
--   MarkovProcess: mem_range_ofContinuousPath_iff
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Lifetime_Law_b2011c24
import Definitions.Def_MarkovProcess_V3H_Lifetime_NonexplosiveTransport_b1c8e8b2
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Process.Filtration
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Constructions.SumProd

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Transporting nonexplosive lifetime laws to continuous paths

This file constructs the measurable inverse of the infinite-lifetime embedding.  A kernel on
lifetime paths whose lifetime is almost surely infinite therefore gives a canonical kernel on
ordinary continuous paths, independent of the off-support default.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace MarkovProcess

noncomputable section

namespace LifetimePath

variable {alpha : Type*} [TopologicalSpace alpha]









section Measurable

variable [MeasurableSpace alpha] [BorelSpace alpha]

variable [StandardBorelSpace (ContinuousPath alpha)]
  [MeasurableSpace.CountablySeparated (LifetimePath alpha)]



end Measurable
end LifetimePath

namespace Kernel

variable {beta alpha : Type*} [MeasurableSpace beta] [TopologicalSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha]

variable [StandardBorelSpace (ContinuousPath alpha)]
  [MeasurableSpace.CountablySeparated (LifetimePath alpha)]













end Kernel
end
end MarkovProcess


open MarkovProcess
open MarkovProcess.LifetimePath
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Transporting nonexplosive lifetime laws to continuous paths

This file constructs the measurable inverse of the infinite-lifetime embedding.  A kernel on
lifetime paths whose lifetime is almost surely infinite therefore gives a canonical kernel on
ordinary continuous paths, independent of the off-support default.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal




variable {alpha : Type*} [TopologicalSpace alpha]

open MarkovProcess.LifetimePath in

theorem MarkovProcess.LifetimePath.mem_range_ofContinuousPath_iff (omega : LifetimePath alpha) :
    omega ∈ Set.range (ofContinuousPath (α := alpha)) ↔ omega.lifetime = ∞ := by sorry
