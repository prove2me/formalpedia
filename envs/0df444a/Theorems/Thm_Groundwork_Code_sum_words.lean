-- Prove2me | Theorems.Thm_Groundwork_Code_sum_words
-- name    : Groundwork.Code.sum_words
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:15:35.925507+00:00
-- url     : https://prove2.me/theorems/b172ad25-5cae-4d9c-9ca1-6fbb0ea735a5
-- title:
--   Code: sum words
-- statement:
--   The same, over all words of length n.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/Code.lean#L57-L59
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/Code.lean#L57-L59

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Net_Net
import Definitions.Def_StepMachines_Prog_Chunks
import Definitions.Def_StepMachines_Math_Code
set_option autoImplicit false
section
open Groundwork
open Finset
variable {X Y : Type*}
open Groundwork.Code
variable {S : Finset X} {n : ℕ}

theorem Groundwork.Code.sum_words {M : Type*} [AddCommMonoid M] (c : Code S n) (F : X → M) :
    ∑ w ∈ words n, (if w ∈ c.D then F (c.dec w) else 0) = ∑ x ∈ S, F x := by sorry
