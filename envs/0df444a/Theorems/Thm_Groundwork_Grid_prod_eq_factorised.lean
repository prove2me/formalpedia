-- Prove2me | Theorems.Thm_Groundwork_Grid_prod_eq_factorised
-- name    : Groundwork.Grid.prod_eq_factorised
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:17:13.811862+00:00
-- url     : https://prove2.me/theorems/4a9dfccb-1a8c-4cd1-af84-bbdba7d5aefd
-- title:
--   Grid: prod eq factorised
-- statement:
--   An equality factors through the common value; for a family.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Grid/RowNet.lean#L34-L40
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Grid/RowNet.lean#L34-L40

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Grid_Grid
import Definitions.Def_Groundwork_Grid_RowNet
set_option autoImplicit false
section
section
open Groundwork Groundwork.Grid
open Finset
variable {ρ γ α τ : Type}
variable [Fintype ρ] [LinearOrder ρ] [Fintype γ] [LinearOrder γ] [Fintype α] [DecidableEq α]

theorem Groundwork.Grid.prod_eq_factorised {ι β : Type} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β] (x y : ι → β) :
    (∏ i, if x i = y i then (1 : ℤ) else 0) =
      ∑ θ : ι → β, (∏ i, if x i = θ i then 1 else 0) * ∏ i, if y i = θ i then 1 else 0 := by sorry
