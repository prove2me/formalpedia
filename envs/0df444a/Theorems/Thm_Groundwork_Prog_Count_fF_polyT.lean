-- Prove2me | Theorems.Thm_Groundwork_Prog_Count_fF_polyT
-- name    : Groundwork.Prog.Count.fF_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:19:55.415193+00:00
-- url     : https://prove2.me/theorems/3efed680-5399-4036-a4f9-2fa1fdafb76c
-- title:
--   Count: f F poly T
-- statement:
--   The factor of two groups of clauses at a state word and a label word is polynomial-time.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/Count.lean#L63-L63
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/Count.lean#L63-L63

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

theorem Groundwork.Prog.Count.fF_polyT : PolyT (fF g k) := by sorry
