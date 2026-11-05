-- Prove2me | Theorems.Thm_Groundwork_Grid_rowNet_c_le
-- name    : Groundwork.Grid.rowNet_c_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:57:40.176036+00:00
-- url     : https://prove2.me/theorems/d2a59d0c-11ed-4bf0-ae70-8e95a7306891
-- title:
--   Grid: row Net c le
-- statement:
--   Two rows have capacity at most g²mL if every rectangle is charged at most 2mL bits.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Grid/Size.lean#L157-L160
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Grid/Size.lean#L157-L160

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Grid_RowNet
import Definitions.Def_Groundwork_Grid_Expand
import Definitions.Def_Groundwork_Grid_Size
set_option autoImplicit false
section
section
open Groundwork Groundwork.Grid
open Finset
variable {ρ γ α τ : Type}
variable [Fintype ρ] [LinearOrder ρ] [Fintype γ] [LinearOrder γ] [Fintype α] [DecidableEq α]

theorem Groundwork.Grid.rowNet_c_le {g L m : ℕ} (hm : 1 ≤ m) (hγ : Fintype.card γ = g) (R : Inst (ρ × γ) α) (C : Rect ρ γ → Cut α τ)
    (t₀ : τ) (hcap : ∀ ω, (C ω).cap ≤ 2 * m * L) (a b : ρ) : (rowNet R C t₀ L).c a b ≤ g ^ 2 * (m * L) := by sorry
