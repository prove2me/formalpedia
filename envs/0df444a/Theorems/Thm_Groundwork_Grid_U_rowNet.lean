-- Prove2me | Theorems.Thm_Groundwork_Grid_U_rowNet
-- name    : Groundwork.Grid.U_rowNet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:38:51.830645+00:00
-- url     : https://prove2.me/theorems/f68bf073-20c7-400a-b8eb-978af1ce49e7
-- title:
--   Grid: U row Net
-- statement:
--   U counts ordered pairs, so every rectangle counts twice.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Grid/Size.lean#L219-L229
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Grid/Size.lean#L219-L229

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

theorem Groundwork.Grid.U_rowNet {g L : ℕ} (hρ : Fintype.card ρ = g) (hγ : Fintype.card γ = g) (R : Inst (ρ × γ) α)
    (C : Rect ρ γ → Cut α τ) (t₀ : τ) :
    (rowNet R C t₀ L).U = g ^ 2 * (g - 1) * L + 2 * ∑ ω ∈ Ω ρ γ, (C ω).cap := by sorry
