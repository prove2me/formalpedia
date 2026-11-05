-- Prove2me | Theorems.Thm_Groundwork_prod_le_prod_of_nonneg
-- name    : Groundwork.prod_le_prod_of_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:55:47.544843+00:00
-- url     : https://prove2.me/theorems/0a78c840-9762-4925-b66b-b1198fe46555
-- title:
--   Groundwork: prod le prod of nonneg
-- statement:
--   Products of nonnegative factors are monotone.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Net/Net.lean#L38-L44
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Net/Net.lean#L38-L44

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Net_Defs
import Definitions.Def_Groundwork_Net_Calculus
import Definitions.Def_Groundwork_Net_Net
set_option autoImplicit false
section
open Groundwork
open Finset
variable {J J' σ τ A A' : Type*}

theorem Groundwork.prod_le_prod_of_nonneg {ι R : Type*} [CommSemiring R] [PartialOrder R] [IsOrderedRing R] (s : Finset ι)
    (f g : ι → R) (h0 : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i ∈ s, f i ≤ g i) : ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by sorry
