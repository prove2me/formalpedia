-- Prove2me | Theorems.Thm_Groundwork_Prog_NetE_cap_le
-- name    : Groundwork.Prog.NetE.cap_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:58:00.949537+00:00
-- url     : https://prove2.me/theorems/8a9edd3a-e585-4df3-aa18-e3dbb25bb7ac
-- title:
--   Net E: cap le
-- statement:
--   The Net E construction uses the cap le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/NetRun.lean#L50-L54
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/NetRun.lean#L50-L54

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

theorem Groundwork.Prog.NetE.cap_le (hN : Np.Presents c N t S) (hS : N.Sized P B) {a b : Fin g} (hab : a ≠ b) :
    Np.cap c a b ≤ P := by sorry
