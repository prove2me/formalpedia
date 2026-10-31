-- Prove2me | Theorems.Thm_MarkovProcess_ContinuousPath_stoppedPath_stoppedPath
-- name    : MarkovProcess.ContinuousPath.stoppedPath_stoppedPath
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T08:31:42.549441+00:00
-- url     : https://prove2.me/theorems/eb425f30-118c-45cb-a167-186036cd6f17
-- title:
--   MarkovProcess: stoppedPath_stoppedPath
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Path_Basic_736b8012
import Definitions.Def_MarkovProcess_V3H_Path_Stopping_15bd9e0d
import Mathlib.Probability.Process.Filtration
import Mathlib.Topology.CompactOpen

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Deterministic stopping of continuous paths

This file defines stopping a continuous path at a fixed deterministic time. It proves only
topological and Borel-measurability properties of this operation; it introduces no stopping
times or stochastic laws.
-/

namespace MarkovProcess

namespace ContinuousPath

variable {alpha : Type*} [TopologicalSpace alpha]





















end ContinuousPath

end MarkovProcess


open MarkovProcess
open MarkovProcess.ContinuousPath
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Deterministic stopping of continuous paths

This file defines stopping a continuous path at a fixed deterministic time. It proves only
topological and Borel-measurability properties of this operation; it introduces no stopping
times or stochastic laws.
-/



variable {alpha : Type*} [TopologicalSpace alpha]



















open MarkovProcess.ContinuousPath in

@[simp]

theorem MarkovProcess.ContinuousPath.stoppedPath_stoppedPath (S T : NNReal) (omega : ContinuousPath alpha) :
    stoppedPath S (stoppedPath T omega) = stoppedPath (min S T) omega := by sorry
