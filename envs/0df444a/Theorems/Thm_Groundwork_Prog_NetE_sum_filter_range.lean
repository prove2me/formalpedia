-- Prove2me | Theorems.Thm_Groundwork_Prog_NetE_sum_filter_range
-- name    : Groundwork.Prog.NetE.sum_filter_range
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:59:25.301626+00:00
-- url     : https://prove2.me/theorems/ec4a6a2b-32d2-4743-96f0-8c250ed34e36
-- title:
--   Net E: sum filter range
-- statement:
--   The Net E construction uses the sum filter range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/NetVal.lean#L394-L400
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/NetVal.lean#L394-L400

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

theorem Groundwork.Prog.NetE.sum_filter_range (g : ℕ) (p : ℕ → Bool) (f : ℕ → ℕ) :
    (((List.range g).filter p).map f).sum = ∑ b : Fin g with p b.val = true, f b.val := by sorry
