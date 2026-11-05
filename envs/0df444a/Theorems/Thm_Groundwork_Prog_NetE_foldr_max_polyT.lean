-- Prove2me | Theorems.Thm_Groundwork_Prog_NetE_foldr_max_polyT
-- name    : Groundwork.Prog.NetE.foldr_max_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:50:47.927672+00:00
-- url     : https://prove2.me/theorems/c28f626d-99db-4231-b579-fc3d6231e586
-- title:
--   Net E: foldr max poly T
-- statement:
--   The largest number of a list.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/NetFun.lean#L64-L66
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/NetFun.lean#L64-L66

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

theorem Groundwork.Prog.NetE.foldr_max_polyT {l : α → List ℕ} (hl : PolyT l) : PolyT fun x => (l x).foldr max 0 := by sorry
