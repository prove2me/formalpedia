-- Prove2me | Theorems.Thm_Groundwork_Code_card_filter_getD
-- name    : Groundwork.Code.card_filter_getD
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:15:39.344204+00:00
-- url     : https://prove2.me/theorems/ff1c4b8c-2d55-4fd6-955b-6dd6bf948110
-- title:
--   Code: card filter get D
-- statement:
--   The Code construction uses the card filter get D property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/CodeMore.lean#L152-L159
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/CodeMore.lean#L152-L159

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Math_Code
import Mathlib.Data.List.GetD
import Definitions.Def_StepMachines_Math_CodeMore
set_option autoImplicit false
section
open Groundwork
open Finset
variable {X Y : Type*}
open Groundwork.Code
variable {S : Finset X} {n : ℕ}

theorem Groundwork.Code.card_filter_getD (τ : List Bool) : #{j ∈ range τ.length | τ.getD j false = true} = τ.count true := by sorry
