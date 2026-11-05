-- Prove2me | Theorems.Thm_Groundwork_Prog_NetE_div_mod_pair
-- name    : Groundwork.Prog.NetE.div_mod_pair
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:14:48.744996+00:00
-- url     : https://prove2.me/theorems/69f94f8a-25b6-4c8d-a2cb-0c9e0007937f
-- title:
--   Net E: div mod pair
-- statement:
--   The Net E construction uses the div mod pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/NetVal.lean#L233-L237
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/NetVal.lean#L233-L237

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_NetProg
import Definitions.Def_StepMachines_Prog_NetVal
set_option autoImplicit false
section
open Groundwork
open Finset
open Groundwork.Prog Groundwork.Prog.NetE
variable {C : Type} {K g : ℕ} (Np : PNet C)

theorem Groundwork.Prog.NetE.div_mod_pair (a b : Fin g) : (a.val * g + b.val) / g = a.val ∧ (a.val * g + b.val) % g = b.val := by sorry
