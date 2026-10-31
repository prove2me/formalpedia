-- Prove2me | Theorems.Thm_MarkovProcess_CountableEnumeration_prefix_succ
-- name    : MarkovProcess.CountableEnumeration.prefix_succ
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T08:32:47.493368+00:00
-- url     : https://prove2.me/theorems/40f2b903-c165-4c98-af12-29e7734ef6e3
-- title:
--   MarkovProcess: prefix_succ
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Time_CountableDenseTime_721ef7df
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Encodable
import Mathlib.Logic.Denumerable
import Mathlib.MeasureTheory.MeasurableSpace.Embedding

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Countable dense time indices

This file gives finite prefixes and measurable path reindexings for an arbitrary enumeration of
a countably infinite type. The fixed enumeration of nonnegative rational times below is arbitrary,
not increasing. No probability law, projective limit, stochastic process, continuity, or path
regularity is constructed here.
-/

namespace MarkovProcess

noncomputable section

namespace CountableEnumeration

variable {D : Type*}























end CountableEnumeration



namespace DenseTime











end DenseTime
end
end MarkovProcess


open MarkovProcess
open MarkovProcess.CountableEnumeration
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Countable dense time indices

This file gives finite prefixes and measurable path reindexings for an arbitrary enumeration of
a countably infinite type. The fixed enumeration of nonnegative rational times below is arbitrary,
not increasing. No probability law, projective limit, stochastic process, continuity, or path
regularity is constructed here.
-/




variable {D : Type*}







open MarkovProcess.CountableEnumeration in
@[simp]

theorem MarkovProcess.CountableEnumeration.prefix_succ (e : ℕ ≃ D) (n : ℕ) :
    «prefix» e (n + 1) =
      Finset.cons (e n) («prefix» e n) (by
        rw [mem_prefix_iff, e.symm_apply_apply]
        exact Nat.lt_irrefl n) := by sorry
