-- Prove2me | Theorems.Thm_Groundwork_Prog_NetE_chi_eq_iff
-- name    : Groundwork.Prog.NetE.chi_eq_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:58:02.023177+00:00
-- url     : https://prove2.me/theorems/3521be53-ec31-48ca-af90-16ca360f45f9
-- title:
--   Net E: chi eq iff
-- statement:
--   The Net E construction uses the chi eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/NetVal.lean#L261-L262
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/NetVal.lean#L261-L262

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

theorem Groundwork.Prog.NetE.chi_eq_iff (hK : 0 < K) (x : ℕ) (a : Fin g) (G : Fin K) : chi hK x a = G ↔ col K x a = G.val := by sorry
