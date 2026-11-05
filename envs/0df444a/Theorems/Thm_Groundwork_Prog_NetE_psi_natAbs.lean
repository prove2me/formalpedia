-- Prove2me | Theorems.Thm_Groundwork_Prog_NetE_psi_natAbs
-- name    : Groundwork.Prog.NetE.psi_natAbs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:14:40.62278+00:00
-- url     : https://prove2.me/theorems/2ef81283-5e6d-4b04-9a02-8e9c8e359d57
-- title:
--   Net E: psi nat Abs
-- statement:
--   The Net E construction uses the psi nat Abs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/NetRun.lean#L83-L96
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/NetRun.lean#L83-L96

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

theorem Groundwork.Prog.NetE.psi_natAbs (hN : Np.Presents c N t S) (hS : N.Sized P B) {a b : ℕ} (ha : a < g) (hb : b < g)
    (hab : a ≠ b) (z z' : List Bool) :
    (∑ y ∈ range (2 ^ Np.cap c a b), valF N a b z (toWord (Np.cap c a b) y) *
      valF N b a z' (toWord (Np.cap c a b) y)).natAbs ≤ 2 ^ B := by sorry
