-- Prove2me | Theorems.Thm_Groundwork_Grid_Z_eq_symm
-- name    : Groundwork.Grid.Z_eq_symm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:17:11.489781+00:00
-- url     : https://prove2.me/theorems/7200e196-5708-4ac4-93b3-cf9d40540b0d
-- title:
--   Grid: Z eq symm
-- statement:
--   Z in half-edge form.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Grid/Grid.lean#L128-L146
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Grid/Grid.lean#L128-L146

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

theorem Groundwork.Grid.Z_eq_symm [Fintype J] [LinearOrder J] (R : Inst J α) (d : α) :
    R.Z d = ∑ ℓ : J → J → α, (∏ w, if ℓ w w = d then R w (ℓ w) else 0) *
      (if ∀ w w', ℓ w w' = ℓ w' w then 1 else 0) := by sorry
