-- Prove2me | Theorems.Thm_MarkovProcess_DenseTimeHistory_historyEquiv_symm_apply_succ
-- name    : MarkovProcess.DenseTimeHistory.historyEquiv_symm_apply_succ
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T08:31:48.540035+00:00
-- url     : https://prove2.me/theorems/9019575b-64cb-40dc-8e0a-c02796c48bd1
-- title:
--   MarkovProcess: historyEquiv_symm_apply_succ
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

theorem MarkovProcess.DenseTimeHistory.historyEquiv_symm_apply_succ (n : ℕ) (x : α) (path : Fin n → α) (i : Fin n) :
    (historyEquiv n).symm (x, path) ⟨i.succ, i.isLt⟩ = path i := by sorry
