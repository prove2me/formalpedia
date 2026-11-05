-- Prove2me | Theorems.Thm_Groundwork_Prog_NetE_valF_runs
-- name    : Groundwork.Prog.NetE.valF_runs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:14:35.488508+00:00
-- url     : https://prove2.me/theorems/b403e7b5-bd25-4663-b1ae-d9d13a6b8ad3
-- title:
--   Net E: val F runs
-- statement:
--   The Net E construction uses the val F runs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/NetRun.lean#L75-L81
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/NetRun.lean#L75-L81

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

theorem Groundwork.Prog.NetE.valF_runs (hN : Np.Presents c N t S) (hS : N.Sized P B) {a b : ℕ} (ha : a < g) (hb : b < g)
    (hab : a ≠ b) {z θ : List Bool} (hz : z.length = Np.n c a) (hθ : θ.length = Np.cap c a b) :
    Np.f.Runs (c, ((a, b), (z, θ))) t S (valF N a b z θ) ∧ (valF N a b z θ).natAbs ≤ 2 ^ B := by sorry
