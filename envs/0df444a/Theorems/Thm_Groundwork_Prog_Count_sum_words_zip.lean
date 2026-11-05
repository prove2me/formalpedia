-- Prove2me | Theorems.Thm_Groundwork_Prog_Count_sum_words_zip
-- name    : Groundwork.Prog.Count.sum_words_zip
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:22:23.770896+00:00
-- url     : https://prove2.me/theorems/d990561a-5875-4ecb-8e22-1a54be308f8f
-- title:
--   Count: sum words zip
-- statement:
--   One bit a link: the sum over the label words restores the equalities.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/CountNet.lean#L296-L308
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/CountNet.lean#L296-L308

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Spec
import Definitions.Def_StepMachines_Math_SatNet
import Definitions.Def_StepMachines_Prog_CountNet
set_option autoImplicit false
section
open Groundwork Groundwork.Prog
open Finset SatNet
open Groundwork.Prog.Count
variable {g μ k : ℕ} {φ : Fml}

theorem Groundwork.Prog.Count.sum_words_zip {α : Type} (L : List α) (u v : α → Bool) :
    ∑ θ ∈ words L.length, (if ((L.zip θ).all fun p => u p.1 == p.2) then (1 : ℤ) else 0) *
      (if ((L.zip θ).all fun p => v p.1 == p.2) then 1 else 0) = if (L.all fun p => u p == v p) then 1 else 0 := by sorry
