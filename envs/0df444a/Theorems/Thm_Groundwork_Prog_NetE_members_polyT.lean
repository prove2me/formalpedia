-- Prove2me | Theorems.Thm_Groundwork_Prog_NetE_members_polyT
-- name    : Groundwork.Prog.NetE.members_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:49:35.173506+00:00
-- url     : https://prove2.me/theorems/7713bd32-f066-4b14-b3a7-e20eabc77a16
-- title:
--   Net E: members poly T
-- statement:
--   The Net E construction uses the members poly T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/NetFun.lean#L88-L90
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/NetFun.lean#L88-L90

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

theorem Groundwork.Prog.NetE.members_polyT {x G : α → ℕ} (hx : PolyT x) (hG : PolyT G) :
    PolyT fun t => members K g (x t) (G t) := by sorry
