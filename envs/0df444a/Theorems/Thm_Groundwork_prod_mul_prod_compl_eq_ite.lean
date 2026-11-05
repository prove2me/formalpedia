-- Prove2me | Theorems.Thm_Groundwork_prod_mul_prod_compl_eq_ite
-- name    : Groundwork.prod_mul_prod_compl_eq_ite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:16:09.3879+00:00
-- url     : https://prove2.me/theorems/0b574e3d-59d8-4c59-b54b-73f2827c77a9
-- title:
--   Groundwork: prod mul prod compl eq ite
-- statement:
--   A product over S times a product over the complement of S, as one product over all positions.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Cross/Cuts.lean#L83-L88
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Cross/Cuts.lean#L83-L88

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_NetworkStatements
import Definitions.Def_Groundwork_Cross_Bit
import Definitions.Def_Groundwork_Cross_Cuts
set_option autoImplicit false
section
section
open Groundwork
open Finset

theorem Groundwork.prod_mul_prod_compl_eq_ite {n : ℕ} (S : Finset (Fin n)) (g1 g0 : Fin n → ℤ) :
    (∏ k ∈ S, g1 k) * ∏ k ∈ Sᶜ, g0 k = ∏ k, if k ∈ S then g1 k else g0 k := by sorry
