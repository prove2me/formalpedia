-- Prove2me | Theorems.Thm_MarkovProcess_LifetimePath_isStoppingTime_exitTime
-- name    : MarkovProcess.LifetimePath.isStoppingTime_exitTime
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:30:38.627139+00:00
-- url     : https://prove2.me/theorems/9467cd49-343e-443d-aa74-3944951cbad0
-- title:
--   MarkovProcess: isStoppingTime_exitTime
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Lifetime_ExitTimeStopping_1c91d085
import Definitions.Def_MarkovProcess_V3H_Lifetime_ExitTime_a7b75085
import Definitions.Def_MarkovProcess_V3H_Lifetime_Filtration_a21e5dcd
import Definitions.Def_MarkovProcess_V3H_Path_ClosedSetDetection_642089d8
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Encodable
import Mathlib.Logic.Denumerable
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-! # Exit times as stopping times -/

open MeasureTheory Set
open scoped ENNReal

namespace MarkovProcess.LifetimePath

noncomputable section

variable {alpha : Type*} [PseudoMetricSpace alpha]















section Measurable

variable [MeasurableSpace alpha] [BorelSpace alpha]









end Measurable

end
end MarkovProcess.LifetimePath


open MarkovProcess
open MarkovProcess.LifetimePath
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-! # Exit times as stopping times -/

open MeasureTheory Set
open scoped ENNReal



variable {alpha : Type*} [PseudoMetricSpace alpha]
















variable [MeasurableSpace alpha] [BorelSpace alpha]







open MarkovProcess.LifetimePath in

theorem MarkovProcess.LifetimePath.isStoppingTime_exitTime (U : Set alpha) (hU : IsOpen U) :
    IsStoppingTime (canonicalFiltration (alpha := alpha)) (exitTime U) := by sorry
