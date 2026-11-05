-- Prove2me | Theorems.Thm_Groundwork_cut_take
-- name    : Groundwork.cut_take
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:14:44.740307+00:00
-- url     : https://prove2.me/theorems/7b780774-465f-46f9-8f58-a00e8ecc1f8c
-- title:
--   Groundwork: cut take
-- statement:
--   cut reads only the first Σ c i bits.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/NetVal.lean#L82-L88
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/NetVal.lean#L82-L88

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_NetProg
import Definitions.Def_StepMachines_Prog_NetVal
set_option autoImplicit false
section
open Groundwork
open Finset

theorem Groundwork.cut_take {ι : Type*} [DecidableEq ι] (c : ι → ℕ) (d : List Bool) (e : List ι) (w : List Bool) :
    cut c d e (w.take (e.map c).sum) = cut c d e w := by sorry
