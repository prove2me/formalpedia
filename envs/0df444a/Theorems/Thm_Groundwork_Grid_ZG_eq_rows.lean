-- Prove2me | Theorems.Thm_Groundwork_Grid_ZG_eq_rows
-- name    : Groundwork.Grid.ZG_eq_rows
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:17:12.838805+00:00
-- url     : https://prove2.me/theorems/02ae27df-c3bd-4fb3-84cc-1ccca9357bfe
-- title:
--   Grid: ZG eq rows
-- statement:
--   Regrouping the half-edges by the row of their source.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Grid/RowNet.lean#L24-L31
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Grid/RowNet.lean#L24-L31

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

theorem Groundwork.Grid.ZG_eq_rows (R : Inst (ρ × γ) α) (G : Rect ρ γ → α → α → α → α → ℤ) :
    ZG R G = ∑ z : ρ → RowSt ρ γ α, (∏ a, rowW R a (z a)) * ∏ p ∈ pairs ρ, rowΨ G p.1 p.2 (z p.1) (z p.2) := by sorry
