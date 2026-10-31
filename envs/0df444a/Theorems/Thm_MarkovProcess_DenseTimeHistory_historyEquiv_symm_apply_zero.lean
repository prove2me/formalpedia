-- Prove2me | Theorems.Thm_MarkovProcess_DenseTimeHistory_historyEquiv_symm_apply_zero
-- name    : MarkovProcess.DenseTimeHistory.historyEquiv_symm_apply_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T08:31:49.077641+00:00
-- url     : https://prove2.me/theorems/67bd7ae1-e686-44d1-8d79-d1c6ef571370
-- title:
--   MarkovProcess: historyEquiv_symm_apply_zero
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

theorem MarkovProcess.DenseTimeHistory.historyEquiv_symm_apply_zero (n : ℕ) (x : α) (path : Fin n → α) :
    (historyEquiv n).symm (x, path) ⟨0, Nat.zero_le n⟩ = x := by sorry
