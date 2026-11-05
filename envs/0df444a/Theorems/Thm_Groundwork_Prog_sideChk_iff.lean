-- Prove2me | Theorems.Thm_Groundwork_Prog_sideChk_iff
-- name    : Groundwork.Prog.sideChk_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:23:52.30595+00:00
-- url     : https://prove2.me/theorems/49eb5ea2-8db5-4537-bde5-4f6555c6d5dd
-- title:
--   Prog: side Chk iff
-- statement:
--   The test of sideWP, spelled out.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/SidePresents.lean#L59-L68
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/SidePresents.lean#L59-L68

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Side
import Definitions.Def_StepMachines_Prog_SideBasics
import Definitions.Def_StepMachines_Prog_GridCount
import Definitions.Def_StepMachines_Prog_SidePresents
set_option autoImplicit false
section
section
open Groundwork Groundwork.Prog
open Finset Stepped
open Groundwork.Grid (he node c2 sideN sideCap)

theorem Groundwork.Prog.sideChk_iff {C : Type} {g : ℕ} {tr : Bool} {lam : C → ℕ} (x : (C × ℕ) × WQ) :
    sideChk g tr lam x = true ↔
      (∀ i : Fin g, (he g (lam x.1.1) x.2.2 i (node g tr x.2.1 i)).all (!·) = true) ∧
      ∀ q ∈ pairs (Fin g),
        he g (lam x.1.1) x.2.2 q.1 (node g tr x.2.1 q.2) = he g (lam x.1.1) x.2.2 q.2 (node g tr x.2.1 q.1) := by sorry
