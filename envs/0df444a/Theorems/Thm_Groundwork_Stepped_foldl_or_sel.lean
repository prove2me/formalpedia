-- Prove2me | Theorems.Thm_Groundwork_Stepped_foldl_or_sel
-- name    : Groundwork.Stepped.foldl_or_sel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:23:08.036247+00:00
-- url     : https://prove2.me/theorems/d6ae4a8b-5025-4163-9cba-6e87f816fd22
-- title:
--   Stepped: foldl or sel
-- statement:
--   The Stepped construction uses the foldl or sel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Walk.lean#L62-L68
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Walk.lean#L62-L68

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Stepped
import Definitions.Def_StepMachines_Math_SparsifyTree
import Definitions.Def_StepMachines_Prog_Walk
set_option autoImplicit false
section
open Groundwork Groundwork.Stepped
open Groundwork.Sparsify (leaves)
variable {α β τ ν : Type}

theorem Groundwork.Stepped.foldl_or_sel (sel : τ → Option ν) (v : ν → Bool) (xs : List τ) (c : Bool) :
    xs.foldl (fun c x => c || ((sel x).map v).getD false) c = (c || (xs.filterMap sel).any v) := by sorry
