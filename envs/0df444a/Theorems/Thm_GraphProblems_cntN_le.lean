-- Prove2me | Theorems.Thm_GraphProblems_cntN_le
-- name    : GraphProblems.cntN_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:03:57.07043+00:00
-- url     : https://prove2.me/theorems/7a621525-ad54-42cd-9aa1-f41358f14c31
-- title:
--   Graph Problems: cnt N le
-- statement:
--   The Graph Problems construction uses the cnt N le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/GraphProblems/Sized.lean#L73-L75
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/GraphProblems/Sized.lean#L73-L75

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GraphProblems_Interfaces
import Definitions.Def_GraphProblems_Engine
import Definitions.Def_GraphProblems_Cert
import Definitions.Def_ToTuring_Poly_Range
import Definitions.Def_ToTuring_Machine_EndTM
import Definitions.Def_StepMachines_Prog_Sat
import Definitions.Def_StepMachines_Prog_Sat
import Definitions.Def_StepMachines_Prog_Decode
import Definitions.Def_StepMachines_Prog_Decode
import Definitions.Def_WidthK_Top_Sat
import Definitions.Def_WidthK_Top_Sat
import Mathlib.Tactic
import Definitions.Def_GraphProblems_Sized
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
open GraphProblems
open Groundwork Groundwork.Prog Groundwork.Stepped CountKSat Finset

theorem GraphProblems.cntN_le (N : ℕ) (ψ : Fml) : cntN N ψ ≤ 2 ^ N := by sorry
