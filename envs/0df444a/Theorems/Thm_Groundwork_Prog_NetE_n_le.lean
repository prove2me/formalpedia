-- Prove2me | Theorems.Thm_Groundwork_Prog_NetE_n_le
-- name    : Groundwork.Prog.NetE.n_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:58:09.74353+00:00
-- url     : https://prove2.me/theorems/91486719-2f0b-4e25-b2c7-21deb4742d65
-- title:
--   Net E: n le
-- statement:
--   The Net E construction uses the n le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/NetRun.lean#L45-L48
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/NetRun.lean#L45-L48

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

theorem Groundwork.Prog.NetE.n_le (hN : Np.Presents c N t S) (hS : N.Sized P B) (a : Fin g) : Np.n c a ≤ P := by sorry
