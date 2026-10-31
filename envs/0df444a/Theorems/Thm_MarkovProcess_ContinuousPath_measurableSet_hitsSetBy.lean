-- Prove2me | Theorems.Thm_MarkovProcess_ContinuousPath_measurableSet_hitsSetBy
-- name    : MarkovProcess.ContinuousPath.measurableSet_hitsSetBy
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:26:11.574586+00:00
-- url     : https://prove2.me/theorems/a1db69a1-3c26-4f77-a465-e50673736627
-- title:
--   MarkovProcess: measurableSet_hitsSetBy
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

























variable [MeasurableSpace alpha] [BorelSpace alpha]



open MarkovProcess.ContinuousPath in

theorem MarkovProcess.ContinuousPath.measurableSet_hitsSetBy (t : NNReal) (F : Set alpha) (hF : IsClosed F) :
    MeasurableSet[canonicalFiltration (alpha := alpha) t] (hitsSetBy t F) := by sorry
