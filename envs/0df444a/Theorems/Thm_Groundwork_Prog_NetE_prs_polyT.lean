-- Prove2me | Theorems.Thm_Groundwork_Prog_NetE_prs_polyT
-- name    : Groundwork.Prog.NetE.prs_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:48:06.687908+00:00
-- url     : https://prove2.me/theorems/56ceb2f4-7b65-41df-923e-8f96c03ce668
-- title:
--   Net E: prs poly T
-- statement:
--   The Net E construction uses the prs poly T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/NetFun.lean#L92-L94
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/NetFun.lean#L92-L94

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Poly_Spec
import Definitions.Def_ToTuring_Lib_Int
import Definitions.Def_StepMachines_Prog_NetProg
import Definitions.Def_ToTuring_Poly_NetFun
set_option autoImplicit false
section
section
open Groundwork Groundwork.Prog Groundwork.Prog.NetE
variable {α β : Type} [Enc α] [Enc β]
variable (K g : ℕ)

theorem Groundwork.Prog.NetE.prs_polyT {x G G' : α → ℕ} (hx : PolyT x) (hG : PolyT G) (hG' : PolyT G') :
    PolyT fun t => prs K g (x t) (G t) (G' t) := by sorry
