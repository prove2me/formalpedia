-- Prove2me | Theorems.Thm_Groundwork_Prog_size_list_le
-- name    : Groundwork.Prog.size_list_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:35:49.755357+00:00
-- url     : https://prove2.me/theorems/355e77e7-0316-419b-ab63-a749ba2a449b
-- title:
--   Prog: size list le
-- statement:
--   The Prog construction uses the size list le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Sat.lean#L55-L58
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Sat.lean#L55-L58

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

theorem Groundwork.Prog.size_list_le {α : Type} [HasSize α] {l : List α} {k s : ℕ} (hl : l.length ≤ k)
    (hs : ∀ x ∈ l, size x ≤ s) : size l ≤ k * (s + 1) + 1 := by sorry
