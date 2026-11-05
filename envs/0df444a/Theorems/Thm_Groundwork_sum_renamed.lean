-- Prove2me | Theorems.Thm_Groundwork_sum_renamed
-- name    : Groundwork.sum_renamed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:13:35.249373+00:00
-- url     : https://prove2.me/theorems/af7a0828-9d39-4101-b40f-c3548ec1d2aa
-- title:
--   Groundwork: sum renamed
-- statement:
--   (b): labels may be renamed into a larger type, both factors vanishing off the set D of names.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Net/Calculus.lean#L69-L77
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Net/Calculus.lean#L69-L77

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

theorem Groundwork.sum_renamed [Fintype A] [DecidableEq A] (D : Finset A) (dec : A → τ) (Θ : Finset τ)
    (h : Set.BijOn dec D Θ) (f f' : τ → ℤ) :
    ∑ x, (if x ∈ D then f (dec x) else 0) * (if x ∈ D then f' (dec x) else 0) = ∑ θ ∈ Θ, f θ * f' θ := by sorry
