-- Prove2me | Theorems.Thm_Groundwork_Grid_value_rowNet
-- name    : Groundwork.Grid.value_rowNet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:38:38.612536+00:00
-- url     : https://prove2.me/theorems/41fe363c-9d62-4f50-ba0a-3e68b607effc
-- title:
--   Grid: value row Net
-- statement:
--   The row network has the value ZG.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Grid/RowNet.lean#L63-L70
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Grid/RowNet.lean#L63-L70

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

theorem Groundwork.Grid.value_rowNet {G : Rect ρ γ → α → α → α → α → ℤ} {C : Rect ρ γ → Cut α τ} (h : ∀ ω, (C ω).Factors (G ω))
    (R : Inst (ρ × γ) α) (t₀ : τ) (L : ℕ) : (rowNet R C t₀ L).value = ZG R G := by sorry
