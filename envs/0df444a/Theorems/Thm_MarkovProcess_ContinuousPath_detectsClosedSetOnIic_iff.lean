-- Prove2me | Theorems.Thm_MarkovProcess_ContinuousPath_detectsClosedSetOnIic_iff
-- name    : MarkovProcess.ContinuousPath.detectsClosedSetOnIic_iff
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T08:30:55.033439+00:00
-- url     : https://prove2.me/theorems/2e9acd73-029b-430c-b3c4-282bcc4ecdbf
-- title:
--   MarkovProcess: detectsClosedSetOnIic_iff
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Path_Basic_736b8012
import Definitions.Def_MarkovProcess_V3H_Path_ClosedSetDetection_642089d8
import Definitions.Def_MarkovProcess_V3H_Time_CountableDenseTime_721ef7df
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Encodable
import Mathlib.Logic.Denumerable
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.Probability.Process.Filtration
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-! # Detecting closed sets from countably many path coordinates -/

open MeasureTheory Set

namespace MarkovProcess

noncomputable section

namespace ContinuousPath

variable {alpha : Type*} [PseudoMetricSpace alpha]

























variable [MeasurableSpace alpha] [BorelSpace alpha]





end ContinuousPath

end
end MarkovProcess


open MarkovProcess
open MarkovProcess.ContinuousPath
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-! # Detecting closed sets from countably many path coordinates -/

open MeasureTheory Set




variable {alpha : Type*} [PseudoMetricSpace alpha]









open MarkovProcess.ContinuousPath in

theorem MarkovProcess.ContinuousPath.detectsClosedSetOnIic_iff
    (t : NNReal) (F : Set alpha) (hF : IsClosed F) (f : C(Set.Iic t, alpha)) :
    DetectsClosedSetOnIic t F f ↔ ∃ s : Set.Iic t, f s ∈ F := by sorry
