-- Prove2me | Theorems.Thm_Groundwork_Prog_NetE_rowSum_eq
-- name    : Groundwork.Prog.NetE.rowSum_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:59:01.85365+00:00
-- url     : https://prove2.me/theorems/8c7a992c-80dc-4b99-a2e5-78e32bb98b80
-- title:
--   Net E: row Sum eq
-- statement:
--   The Net E construction uses the row Sum eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/NetVal.lean#L419-L423
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/NetVal.lean#L419-L423

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
variable {c : C} {N : Network (Fin g) (List Bool) (List Bool)} {t S : ℕ}

theorem Groundwork.Prog.NetE.rowSum_eq (hN : Np.Presents c N t S) (a : Fin g) : rowSum g Np c a.val = ∑ b ∈ univ.erase a, N.c a b := by sorry
