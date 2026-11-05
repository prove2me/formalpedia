-- Prove2me | Theorems.Thm_Groundwork_Prog_Count_mu_le_length
-- name    : Groundwork.Prog.Count.mu_le_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:57:39.986607+00:00
-- url     : https://prove2.me/theorems/c781591e-f52b-4739-9147-7bfc537cbb6d
-- title:
--   Count: mu le length
-- statement:
--   A group has at most as many clauses as the formula, for every g (`mu_le` of
--   StepMachines/Prog/CountNet.lean needs 0 < g).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/Count.lean#L72-L75
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/Count.lean#L72-L75

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Poly_Spec
import Definitions.Def_ToTuring_Poly_IsPoly
import Definitions.Def_ToTuring_Lib_List3
import Definitions.Def_StepMachines_Prog_Count
import Definitions.Def_ToTuring_Poly_Count
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open Groundwork Groundwork.Prog Groundwork.Prog.Count
variable {α : Type} [Enc α] (g k : ℕ)

theorem Groundwork.Prog.Count.mu_le_length (φ : Fml) : mu g φ ≤ φ.length := by sorry
