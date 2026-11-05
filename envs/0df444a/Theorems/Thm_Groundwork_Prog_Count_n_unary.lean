-- Prove2me | Theorems.Thm_Groundwork_Prog_Count_n_unary
-- name    : Groundwork.Prog.Count.n_unary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:19:49.556765+00:00
-- url     : https://prove2.me/theorems/06b917cc-4b5e-4881-9c73-8e5538121dbc
-- title:
--   Count: n unary
-- statement:
--   The number of state bits of a group is given in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/Count.lean#L78-L81
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/Count.lean#L78-L81

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Poly_Spec
import Definitions.Def_ToTuring_Poly_IsPoly
import Definitions.Def_ToTuring_Lib_List3
import Definitions.Def_StepMachines_Prog_Count
import Definitions.Def_ToTuring_Poly_Count
set_option autoImplicit false
section
section
open Groundwork Groundwork.Prog Groundwork.Prog.Count
variable {α : Type} [Enc α] (g k : ℕ)

theorem Groundwork.Prog.Count.n_unary : Unary fun p : Fml × ℕ => mu g p.1 * k := by sorry
