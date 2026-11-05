-- Prove2me | Theorems.Thm_Groundwork_Prog_NetE_size_word
-- name    : Groundwork.Prog.NetE.size_word
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:58:08.030688+00:00
-- url     : https://prove2.me/theorems/12bd781b-99af-4c4f-9edc-1f4c85831031
-- title:
--   Net E: size word
-- statement:
--   The Net E construction uses the size word property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/NetRun.lean#L114-L117
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/NetRun.lean#L114-L117

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_NetProg
import Definitions.Def_StepMachines_Prog_NetRun
set_option autoImplicit false
section
open Groundwork Groundwork.Prog Groundwork.Prog.NetE
open Finset Stepped
variable {C : Type} (K g : ℕ) (Np : PNet C)
variable {K g Np} {c : C} {N : Network (Fin g) (List Bool) (List Bool)} {P B t S : ℕ}

theorem Groundwork.Prog.NetE.size_word (l : List Bool) : size l = 2 * l.length + 1 := by sorry
