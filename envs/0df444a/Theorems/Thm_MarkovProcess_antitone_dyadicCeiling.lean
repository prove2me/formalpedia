-- Prove2me | Theorems.Thm_MarkovProcess_antitone_dyadicCeiling
-- name    : MarkovProcess.antitone_dyadicCeiling
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:25:32.181501+00:00
-- url     : https://prove2.me/theorems/e3db3851-803d-43da-beb3-8bdc32faccdb
-- title:
--   MarkovProcess: antitone_dyadicCeiling
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Path_StoppingTimeDyadicCeiling_2d75c809
import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.Instances.NNReal.Lemmas

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Dyadic ceiling approximation of finite stopping times

The level-`n` dyadic ceiling of a nonnegative time is the least point of the grid `2⁻ⁿ ℕ` that is
at least the time.  Composed with a finite `NNReal`-valued stopping time it produces stopping
times with countable range that decrease to the original time.  This is ordinary stopping-time
infrastructure and proves no restart identity; the restart identity obtained from this
approximation is in `Trajectory/FellerStoppingRestart.lean`.
-/

open MeasureTheory Filter Topology
open scoped NNReal

namespace MarkovProcess

noncomputable section





































variable {Omega : Type*} {m : MeasurableSpace Omega}









end

end MarkovProcess


open MarkovProcess
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Dyadic ceiling approximation of finite stopping times

The level-`n` dyadic ceiling of a nonnegative time is the least point of the grid `2⁻ⁿ ℕ` that is
at least the time.  Composed with a finite `NNReal`-valued stopping time it produces stopping
times with countable range that decrease to the original time.  This is ordinary stopping-time
infrastructure and proves no restart identity; the restart identity obtained from this
approximation is in `Trajectory/FellerStoppingRestart.lean`.
-/

open MeasureTheory Filter Topology
open scoped NNReal























open MarkovProcess in

theorem MarkovProcess.antitone_dyadicCeiling (t : NNReal) : Antitone fun n ↦ dyadicCeiling n t := by sorry
