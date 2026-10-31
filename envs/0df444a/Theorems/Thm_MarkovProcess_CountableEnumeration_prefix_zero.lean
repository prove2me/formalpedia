-- Prove2me | Theorems.Thm_MarkovProcess_CountableEnumeration_prefix_zero
-- name    : MarkovProcess.CountableEnumeration.prefix_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T08:31:40.406794+00:00
-- url     : https://prove2.me/theorems/fa5237fa-2456-44b2-a91e-c75fdc8d0220
-- title:
--   MarkovProcess: prefix_zero
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

theorem MarkovProcess.CountableEnumeration.prefix_zero (e : ℕ ≃ D) : «prefix» e 0 = ∅ := by sorry
