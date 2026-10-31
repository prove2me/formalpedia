-- Prove2me | Theorems.Thm_MarkovProcess_ContinuousPath_measurableSet_range_denseRestriction
-- name    : MarkovProcess.ContinuousPath.measurableSet_range_denseRestriction
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T08:31:14.199655+00:00
-- url     : https://prove2.me/theorems/f77293e3-e24f-4a92-995f-163a0fef4e3b
-- title:
--   MarkovProcess: measurableSet_range_denseRestriction
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Continuity_DenseTimeContinuousExtension_479df42c
import Definitions.Def_MarkovProcess_V3H_Path_Basic_736b8012
import Definitions.Def_MarkovProcess_V3H_Time_CountableDenseTime_721ef7df
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
# Continuous extension from dense-time paths

This file embeds ordinary continuous paths into paths on the fixed dense time carrier. It proves
that the image is measurable and supplies a measurable total inverse. The inverse is the genuine
continuous extension on the image and is arbitrarily equal to a caller-supplied default path away
from the image.

No probability law is shown to be supported on this image, and no continuous modification,
stochastic-process association, or path-regularity claim is made here.
-/

open MeasureTheory Set

namespace MarkovProcess

noncomputable section

namespace ContinuousPath

variable {alpha : Type*} [TopologicalSpace alpha]

















section Measurable

variable [MeasurableSpace alpha] [BorelSpace alpha]



variable [T2Space alpha] [StandardBorelSpace (ContinuousPath alpha)]
  [MeasurableSpace.CountablySeparated (DenseTime → alpha)]







end Measurable
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

/-!
# Continuous extension from dense-time paths

This file embeds ordinary continuous paths into paths on the fixed dense time carrier. It proves
that the image is measurable and supplies a measurable total inverse. The inverse is the genuine
continuous extension on the image and is arbitrarily equal to a caller-supplied default path away
from the image.

No probability law is shown to be supported on this image, and no continuous modification,
stochastic-process association, or path-regularity claim is made here.
-/

open MeasureTheory Set




variable {alpha : Type*} [TopologicalSpace alpha]


















variable [MeasurableSpace alpha] [BorelSpace alpha]



variable [T2Space alpha] [StandardBorelSpace (ContinuousPath alpha)]
  [MeasurableSpace.CountablySeparated (DenseTime → alpha)]



open MarkovProcess.ContinuousPath in

theorem MarkovProcess.ContinuousPath.measurableSet_range_denseRestriction :
    MeasurableSet (Set.range (denseRestriction (alpha := alpha))) := by sorry
