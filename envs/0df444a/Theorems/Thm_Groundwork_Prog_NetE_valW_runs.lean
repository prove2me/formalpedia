-- Prove2me | Theorems.Thm_Groundwork_Prog_NetE_valW_runs
-- name    : Groundwork.Prog.NetE.valW_runs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:14:29.906676+00:00
-- url     : https://prove2.me/theorems/800a0fae-338f-47aa-9c3e-5683290033af
-- title:
--   Net E: val W runs
-- statement:
--   The Net E construction uses the val W runs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/NetRun.lean#L69-L73
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/NetRun.lean#L69-L73

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

theorem Groundwork.Prog.NetE.valW_runs (hN : Np.Presents c N t S) (hS : N.Sized P B) {a : ℕ} (ha : a < g) {z : List Bool}
    (hz : z.length = Np.n c a) : Np.W.Runs (c, (a, z)) t S (valW N a z) ∧ (valW N a z).natAbs ≤ 2 ^ B := by sorry
