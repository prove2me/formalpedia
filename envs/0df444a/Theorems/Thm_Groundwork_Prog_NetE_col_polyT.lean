-- Prove2me | Theorems.Thm_Groundwork_Prog_NetE_col_polyT
-- name    : Groundwork.Prog.NetE.col_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:47:56.887593+00:00
-- url     : https://prove2.me/theorems/1fc234b9-7b1f-4822-8e4f-9be8de41911b
-- title:
--   Net E: col poly T
-- statement:
--   The Net E construction uses the col poly T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/NetFun.lean#L85-L86
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/NetFun.lean#L85-L86

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

theorem Groundwork.Prog.NetE.col_polyT {x a : α → ℕ} (hx : PolyT x) (ha : PolyT a) : PolyT fun t => col K (x t) (a t) := by sorry
