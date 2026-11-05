-- Prove2me | Theorems.Thm_Groundwork_Prog_Count_capF_unary
-- name    : Groundwork.Prog.Count.capF_unary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:19:26.846568+00:00
-- url     : https://prove2.me/theorems/82cb428e-045e-4045-9f6f-4075b7765c28
-- title:
--   Count: cap F unary
-- statement:
--   The number of label bits of two groups is given in unary: it is the length of the list of their
--   links.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/Count.lean#L67-L68
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/Count.lean#L67-L68

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

theorem Groundwork.Prog.Count.capF_unary : Unary fun p : Fml × ℕ × ℕ => capF g k p.1 p.2.1 p.2.2 := by sorry
