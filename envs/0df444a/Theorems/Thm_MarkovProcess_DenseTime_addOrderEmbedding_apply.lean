-- Prove2me | Theorems.Thm_MarkovProcess_DenseTime_addOrderEmbedding_apply
-- name    : MarkovProcess.DenseTime.addOrderEmbedding_apply
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T08:31:49.372035+00:00
-- url     : https://prove2.me/theorems/f565c93d-ceec-4d41-b2a7-4d3a6165cb5e
-- title:
--   MarkovProcess: addOrderEmbedding_apply
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Continuity_DenseTimeContinuousExtension_479df42c
import Definitions.Def_MarkovProcess_V3H_DenseTime_Shift_b3e2f7d9
import Definitions.Def_MarkovProcess_V3H_Path_Shift_e538a06a
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Encodable
import Mathlib.Logic.Denumerable
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.Probability.Process.Filtration
import Mathlib.Topology.CompactOpen

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Shifts of dense-time paths

This file defines addition by a nonnegative rational time on the fixed dense carrier and the
induced shift of dense-time paths.  Restriction of a continuous path commutes with this shift.
No probability law or Markov property is asserted.
-/

namespace MarkovProcess

noncomputable section

namespace DenseTime







end DenseTime

namespace DenseTimePath

variable {alpha : Type*}









variable [MeasurableSpace alpha]



end DenseTimePath

namespace ContinuousPath

variable {alpha : Type*} [TopologicalSpace alpha]



end ContinuousPath
end
end MarkovProcess


open MarkovProcess
open MarkovProcess.DenseTime
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Shifts of dense-time paths

This file defines addition by a nonnegative rational time on the fixed dense carrier and the
induced shift of dense-time paths.  Restriction of a continuous path commutes with this shift.
No probability law or Markov property is asserted.
-/






open MarkovProcess.DenseTime in
@[simp]

theorem MarkovProcess.DenseTime.addOrderEmbedding_apply (s t : DenseTime) : addOrderEmbedding s t = s + t := by sorry
