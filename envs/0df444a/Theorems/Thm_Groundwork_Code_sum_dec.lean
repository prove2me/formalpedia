-- Prove2me | Theorems.Thm_Groundwork_Code_sum_dec
-- name    : Groundwork.Code.sum_dec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:42:22.675196+00:00
-- url     : https://prove2.me/theorems/d4e368ff-70dc-4fcf-bc18-85b6718d4925
-- title:
--   Code: sum dec
-- statement:
--   A sum over S is the sum over the names.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/Code.lean#L50-L54
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/Code.lean#L50-L54

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

theorem Groundwork.Code.sum_dec {M : Type*} [AddCommMonoid M] (c : Code S n) (F : X → M) :
    ∑ w ∈ c.D, F (c.dec w) = ∑ x ∈ S, F x := by sorry
