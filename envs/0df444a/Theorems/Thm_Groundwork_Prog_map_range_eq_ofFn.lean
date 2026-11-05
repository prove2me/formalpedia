-- Prove2me | Theorems.Thm_Groundwork_Prog_map_range_eq_ofFn
-- name    : Groundwork.Prog.map_range_eq_ofFn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:29:26.70583+00:00
-- url     : https://prove2.me/theorems/3b4dc339-04b3-4757-818d-c84c570b3fee
-- title:
--   Prog: map range eq of Fn
-- statement:
--   The Prog construction uses the map range eq of Fn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/SideBasics.lean#L36-L37
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/SideBasics.lean#L36-L37

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Spec
import Definitions.Def_StepMachines_Prog_Comb
import Definitions.Def_StepMachines_Prog_SideBasics
set_option autoImplicit false
section
section
open Groundwork Groundwork.Prog
open Finset Stepped

theorem Groundwork.Prog.map_range_eq_ofFn {α : Type} (n : ℕ) (f : ℕ → α) : (List.range n).map f = List.ofFn fun u : Fin n => f u := by sorry
