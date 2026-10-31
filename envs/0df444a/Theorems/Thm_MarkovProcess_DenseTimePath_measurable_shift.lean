-- Prove2me | Theorems.Thm_MarkovProcess_DenseTimePath_measurable_shift
-- name    : MarkovProcess.DenseTimePath.measurable_shift
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T08:31:54.719785+00:00
-- url     : https://prove2.me/theorems/b531e4d6-55c9-4a6e-889e-c1bfe618f346
-- title:
--   MarkovProcess: measurable_shift
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
open MarkovProcess.DenseTimePath
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





variable {alpha : Type*}









variable [MeasurableSpace alpha]

open MarkovProcess.DenseTimePath in

theorem MarkovProcess.DenseTimePath.measurable_shift (s : DenseTime) :
    Measurable (shift s : (DenseTime → alpha) → DenseTime → alpha) := by sorry
