-- Prove2me | Theorems.Thm_Groundwork_idxOf_map_inj
-- name    : Groundwork.idxOf_map_inj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:58:59.564363+00:00
-- url     : https://prove2.me/theorems/56fa786e-ecc4-4fb6-a7e8-e1e14d1fab3c
-- title:
--   Groundwork: idx Of map inj
-- statement:
--   The Groundwork construction uses the idx Of map inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/NetVal.lean#L69-L79
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/NetVal.lean#L69-L79

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_NetProg
import Definitions.Def_StepMachines_Prog_NetVal
set_option autoImplicit false
section
open Groundwork
open Finset

theorem Groundwork.idxOf_map_inj {ι κ : Type*} [BEq ι] [LawfulBEq ι] [BEq κ] [LawfulBEq κ] {f : ι → κ}
    (hf : Function.Injective f) (e : List ι) (i : ι) : (e.map f).idxOf (f i) = e.idxOf i := by sorry
