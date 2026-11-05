-- Prove2me | Theorems.Thm_Groundwork_Grid_Z_eq_ZG_X
-- name    : Groundwork.Grid.Z_eq_ZG_X
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:56:52.522681+00:00
-- url     : https://prove2.me/theorems/1adf4e38-0885-4e3b-a4b5-a6fa4017195a
-- title:
--   Grid: Z eq ZG X
-- statement:
--   The half-edge form on the grid.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Grid/Grid.lean#L149-L160
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Grid/Grid.lean#L149-L160

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Grid_Defs
import Definitions.Def_Groundwork_Net_Net
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_Groundwork_Grid_Grid
set_option autoImplicit false
section
section
open Groundwork Groundwork.Grid
open Finset
variable {J ρ γ α : Type}
variable [Fintype ρ] [LinearOrder ρ] [Fintype γ] [LinearOrder γ] [Fintype α] [DecidableEq α]

theorem Groundwork.Grid.Z_eq_ZG_X [Fintype J] [LinearOrder J] (R : Inst J α) (d : α) (e : J ≃ ρ × γ) :
    R.Z d = ZG (onGrid R d e) (fun _ => Cross.X) := by sorry
