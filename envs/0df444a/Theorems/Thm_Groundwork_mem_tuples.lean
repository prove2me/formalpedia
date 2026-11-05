-- Prove2me | Theorems.Thm_Groundwork_mem_tuples
-- name    : Groundwork.mem_tuples
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:23:11.445877+00:00
-- url     : https://prove2.me/theorems/2f297d68-626c-49e5-b5ad-cdec34955b73
-- title:
--   Groundwork: mem tuples
-- statement:
--   Membership in the set of tuples.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Net/Calculus.lean#L33-L38
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Net/Calculus.lean#L33-L38

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

theorem Groundwork.mem_tuples [Fintype ι] [DecidableEq ι] (P : ι → Prop) [DecidablePred P] (T : ι → Finset X') (d : X')
    (t : ι → X') : t ∈ tuples P T d ↔ ∀ i, (P i → t i ∈ T i) ∧ (¬P i → t i = d) := by sorry
