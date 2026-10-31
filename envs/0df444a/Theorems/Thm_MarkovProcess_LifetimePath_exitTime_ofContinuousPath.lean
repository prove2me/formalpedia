-- Prove2me | Theorems.Thm_MarkovProcess_LifetimePath_exitTime_ofContinuousPath
-- name    : MarkovProcess.LifetimePath.exitTime_ofContinuousPath
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T08:32:39.577624+00:00
-- url     : https://prove2.me/theorems/96994ad4-2f10-4b3a-86ad-e61af07af89a
-- title:
--   MarkovProcess: exitTime_ofContinuousPath
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Lifetime_Basic_6f1c513f
import Definitions.Def_MarkovProcess_V3H_Lifetime_ExitTime_a7b75085
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
# Exit times of lifetime paths

This file defines the first time at which a lifetime path is not a live point of a prescribed
set. Reaching the cemetery state counts as exit. The infimum of the empty set is infinity, so a
path which never exits has infinite exit time.

Only deterministic order properties are proved here. No measurability or stopping-time claim is
made.
-/

open Set
open scoped ENNReal

namespace MarkovProcess

noncomputable section

namespace LifetimePath

variable {alpha : Type*} [TopologicalSpace alpha]









end LifetimePath

namespace ContinuousPath

variable {alpha : Type*} [TopologicalSpace alpha]



end ContinuousPath

namespace LifetimePath

variable {alpha : Type*} [TopologicalSpace alpha]





end LifetimePath

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
# Exit times of lifetime paths

This file defines the first time at which a lifetime path is not a live point of a prescribed
set. Reaching the cemetery state counts as exit. The infimum of the empty set is infinity, so a
path which never exits has infinite exit time.

Only deterministic order properties are proved here. No measurability or stopping-time claim is
made.
-/

open Set
open scoped ENNReal






variable {alpha : Type*} [TopologicalSpace alpha]

open MarkovProcess.LifetimePath in

@[simp]

theorem MarkovProcess.LifetimePath.exitTime_ofContinuousPath (U : Set alpha) (omega : ContinuousPath alpha) :
    exitTime U (ofContinuousPath omega) = ContinuousPath.exitTime U omega := by sorry
