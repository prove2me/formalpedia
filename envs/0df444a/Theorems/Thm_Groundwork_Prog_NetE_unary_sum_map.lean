-- Prove2me | Theorems.Thm_Groundwork_Prog_NetE_unary_sum_map
-- name    : Groundwork.Prog.NetE.unary_sum_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:51:21.513281+00:00
-- url     : https://prove2.me/theorems/a70c792f-bcbc-49f3-9d32-5d4e2af0c976
-- title:
--   Net E: unary sum map
-- statement:
--   A sum of unary numbers over a polynomial-time list is unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/NetFun.lean#L75-L79
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/NetFun.lean#L75-L79

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Poly_Spec
import Definitions.Def_ToTuring_Lib_Int
import Definitions.Def_StepMachines_Prog_NetProg
import Definitions.Def_ToTuring_Poly_NetFun
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum


set_option autoImplicit false
section
section
open Groundwork Groundwork.Prog Groundwork.Prog.NetE
variable {α β : Type} [Enc α] [Enc β]

theorem Groundwork.Prog.NetE.unary_sum_map {f : α → β → ℕ} {l : α → List β} (hf : Unary fun p : α × β => f p.1 p.2) (hl : PolyT l) :
    Unary fun a => ((l a).map (f a)).sum := by sorry
