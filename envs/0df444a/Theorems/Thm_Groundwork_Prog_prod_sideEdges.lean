-- Prove2me | Theorems.Thm_Groundwork_Prog_prod_sideEdges
-- name    : Groundwork.Prog.prod_sideEdges
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:24:00.456054+00:00
-- url     : https://prove2.me/theorems/bf812198-1d01-4e93-a98d-20ba925bb159
-- title:
--   Prog: prod side Edges
-- statement:
--   The test of sideFP, as a product of indicators.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/SidePresents.lean#L99-L105
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/SidePresents.lean#L99-L105

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

theorem Groundwork.Prog.prod_sideEdges {C : Type} {g : ℕ} {tr : Bool} {lam : C → ℕ} (x : (C × ℕ) × FQ) :
    ∏ i : Fin g,
        (if he g (lam x.1.1) x.2.2.1 i (node g tr x.2.1.2 i) = block (lam x.1.1) i x.2.2.2 then (1 : ℤ) else 0) =
      if sideEdges g tr lam x = true then 1 else 0 := by sorry
