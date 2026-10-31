-- Prove2me | Theorems.Thm_MarkovProcess_CountableEnumeration_card_prefix
-- name    : MarkovProcess.CountableEnumeration.card_prefix
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T08:31:37.541347+00:00
-- url     : https://prove2.me/theorems/74da8f88-7b29-4f2f-a837-34d9c1c1b629
-- title:
--   MarkovProcess: card_prefix
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

theorem MarkovProcess.CountableEnumeration.card_prefix (e : ℕ ≃ D) (n : ℕ) : («prefix» e n).card = n := by sorry
