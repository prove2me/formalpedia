-- Prove2me | Theorems.Thm_Groundwork_card_pairs
-- name    : Groundwork.card_pairs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:31:44.709232+00:00
-- url     : https://prove2.me/theorems/676d17ca-5e2b-43e6-a8f0-a44bebe78393
-- title:
--   Groundwork: card pairs
-- statement:
--   The number of pairs a < b.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Net/Calculus.lean#L105-L115
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Net/Calculus.lean#L105-L115

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Net_Defs
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Set.Function
import Definitions.Def_Groundwork_Net_Calculus
set_option autoImplicit false
section
open Groundwork
open Finset
variable {ι X' τ A α : Type*}

theorem Groundwork.card_pairs [Fintype α] [LinearOrder α] : #(pairs α) = (Fintype.card α).choose 2 := by sorry
