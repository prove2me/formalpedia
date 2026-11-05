-- Prove2me | Theorems.Thm_Groundwork_Prog_sum_size_le
-- name    : Groundwork.Prog.sum_size_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:44:20.300673+00:00
-- url     : https://prove2.me/theorems/74cfb81f-e8c4-4d88-946d-43d2179159cf
-- title:
--   Prog: sum size le
-- statement:
--   The Prog construction uses the sum size le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Sat.lean#L45-L53
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Sat.lean#L45-L53

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Count
import Definitions.Def_StepMachines_Prog_Walk
import Definitions.Def_StepMachines_Prog_Comb
import Definitions.Def_StepMachines_Prog_Decode
import Definitions.Def_StepMachines_Math_SparsifyProg
import Definitions.Def_ThreeSatStatement
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_StepMachines_Math_SparsifyCount
import Definitions.Def_StepMachines_Prog_Sat
set_option autoImplicit false
section
open Groundwork Groundwork.Prog
open Groundwork.Sparsify (leaves rootP stepP)

theorem Groundwork.Prog.sum_size_le {α : Type} [HasSize α] {s : ℕ} (l : List α) (hs : ∀ x ∈ l, size x ≤ s) :
    (l.map fun x => size x + 1).sum ≤ l.length * (s + 1) := by sorry
