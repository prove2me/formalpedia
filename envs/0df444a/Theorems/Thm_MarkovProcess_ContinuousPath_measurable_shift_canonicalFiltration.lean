-- Prove2me | Theorems.Thm_MarkovProcess_ContinuousPath_measurable_shift_canonicalFiltration
-- name    : MarkovProcess.ContinuousPath.measurable_shift_canonicalFiltration
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T08:31:15.986695+00:00
-- url     : https://prove2.me/theorems/f5990b9d-feb0-4e75-8500-c672852577d9
-- title:
--   MarkovProcess: measurable_shift_canonicalFiltration
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Path_Basic_736b8012
import Definitions.Def_MarkovProcess_V3H_Path_Shift_e538a06a
import Mathlib.Probability.Process.Filtration
import Mathlib.Topology.CompactOpen

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Deterministic shifts of continuous paths

This file defines translation by a fixed nonnegative time on canonical continuous-path space.
The shift is jointly continuous in the shift time and path for the compact-open topology.  It also
records the corresponding deterministic relation between the canonical filtrations.

No random-time shift, Markov property, strong Markov property, or Hunt-process assertion is made.
-/

open MeasureTheory

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
# Deterministic shifts of continuous paths

This file defines translation by a fixed nonnegative time on canonical continuous-path space.
The shift is jointly continuous in the shift time and path for the compact-open topology.  It also
records the corresponding deterministic relation between the canonical filtrations.

No random-time shift, Markov property, strong Markov property, or Hunt-process assertion is made.
-/

open MeasureTheory


variable {alpha : Type*} [TopologicalSpace alpha]





















open MarkovProcess.ContinuousPath in

theorem MarkovProcess.ContinuousPath.measurable_shift_canonicalFiltration [MeasurableSpace alpha] [BorelSpace alpha]
    (S t : NNReal) :
    Measurable[canonicalFiltration (alpha := alpha) (S + t),
      canonicalFiltration (alpha := alpha) t]
      (shift S : ContinuousPath alpha → ContinuousPath alpha) := by sorry
