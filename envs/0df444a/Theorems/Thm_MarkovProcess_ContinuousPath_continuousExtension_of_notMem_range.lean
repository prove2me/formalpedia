-- Prove2me | Theorems.Thm_MarkovProcess_ContinuousPath_continuousExtension_of_notMem_range
-- name    : MarkovProcess.ContinuousPath.continuousExtension_of_notMem_range
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T08:30:40.426031+00:00
-- url     : https://prove2.me/theorems/90ab2e38-cd25-4b86-9596-5b45742edb93
-- title:
--   MarkovProcess: continuousExtension_of_notMem_range
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















open MarkovProcess.ContinuousPath in
@[simp]

theorem MarkovProcess.ContinuousPath.continuousExtension_of_notMem_range (default : ContinuousPath alpha)
    {x : DenseTime → alpha} (hx : x ∉ Set.range (denseRestriction (alpha := alpha))) :
    continuousExtension (alpha := alpha) default x = default := by sorry
