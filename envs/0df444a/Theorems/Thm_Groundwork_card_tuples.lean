-- Prove2me | Theorems.Thm_Groundwork_card_tuples
-- name    : Groundwork.card_tuples
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:33:07.947268+00:00
-- url     : https://prove2.me/theorems/cb4f1bc1-83aa-4d68-be9a-cdf3063122b1
-- title:
--   Groundwork: card tuples
-- statement:
--   The number of tuples.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Net/Calculus.lean#L41-L46
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Net/Calculus.lean#L41-L46

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

theorem Groundwork.card_tuples [Fintype ι] [DecidableEq ι] (P : ι → Prop) [DecidablePred P] (T : ι → Finset X') (d : X') :
    #(tuples P T d) = ∏ i with P i, #(T i) := by sorry
