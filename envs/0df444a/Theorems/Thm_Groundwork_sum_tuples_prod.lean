-- Prove2me | Theorems.Thm_Groundwork_sum_tuples_prod
-- name    : Groundwork.sum_tuples_prod
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:30:42.182582+00:00
-- url     : https://prove2.me/theorems/edd1afad-f686-43d3-9775-0daac06e12fa
-- title:
--   Groundwork: sum tuples prod
-- statement:
--   Distributivity: a sum over tuples of a product is the product of the sums.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Net/Calculus.lean#L49-L56
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Net/Calculus.lean#L49-L56

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

theorem Groundwork.sum_tuples_prod [Fintype ι] [DecidableEq ι] (P : ι → Prop) [DecidablePred P] (T : ι → Finset X') (d : X')
    (H : ι → X' → ℤ) : ∑ t ∈ tuples P T d, ∏ i with P i, H i (t i) = ∏ i with P i, ∑ x ∈ T i, H i x := by sorry
