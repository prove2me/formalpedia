-- Prove2me | Theorems.Thm_MarkovProcess_DenseTimeHistory_iicEquivFin_symm_apply_val
-- name    : MarkovProcess.DenseTimeHistory.iicEquivFin_symm_apply_val
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T08:31:51.744582+00:00
-- url     : https://prove2.me/theorems/2e4f9076-84f2-468d-8753-4397d0a8e11a
-- title:
--   MarkovProcess: iicEquivFin_symm_apply_val
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Time_DenseTimeHistory_28830881
import Mathlib.MeasureTheory.MeasurableSpace.Embedding

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Finite dense-time histories

This file provides measurable coordinate equivalences for histories indexed by an initial
segment of the natural numbers. It makes no probability-law, kernel, or stochastic-process claim.
-/

namespace MarkovProcess



namespace DenseTimeHistory

variable {α : Type*} [MeasurableSpace α]



























end DenseTimeHistory

end MarkovProcess


open MarkovProcess
open MarkovProcess.DenseTimeHistory
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Finite dense-time histories

This file provides measurable coordinate equivalences for histories indexed by an initial
segment of the natural numbers. It makes no probability-law, kernel, or stochastic-process claim.
-/





variable {α : Type*} [MeasurableSpace α]





open MarkovProcess.DenseTimeHistory in
@[simp]

theorem MarkovProcess.DenseTimeHistory.iicEquivFin_symm_apply_val (n : ℕ) (i : Fin (n + 1)) :
    ((iicEquivFin n).symm i).val = i.val := by sorry
