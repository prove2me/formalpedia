-- Prove2me | Theorems.Thm_Groundwork_Prog_NetE_flatMap_replicate_unit
-- name    : Groundwork.Prog.NetE.flatMap_replicate_unit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:14:21.960021+00:00
-- url     : https://prove2.me/theorems/001673f5-4862-4979-b04b-6dd6cb5be96a
-- title:
--   Net E: flat Map replicate unit
-- statement:
--   The Net E construction uses the flat Map replicate unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/NetFun.lean#L68-L72
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/NetFun.lean#L68-L72

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Poly_Spec
import Definitions.Def_ToTuring_Lib_Int
import Definitions.Def_StepMachines_Prog_NetProg
import Definitions.Def_ToTuring_Poly_NetFun
import Theorems.Thm_Groundwork_PolyT_flatMap
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
attribute [local fun_prop] Groundwork.PolyT.flatMap
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum


set_option autoImplicit false
section
section
open Groundwork Groundwork.Prog Groundwork.Prog.NetE
variable {α β : Type} [Enc α] [Enc β]

theorem Groundwork.Prog.NetE.flatMap_replicate_unit {β : Type} (f : β → ℕ) (l : List β) :
    (l.flatMap fun b => List.replicate (f b) ()) = List.replicate (l.map f).sum () := by sorry
