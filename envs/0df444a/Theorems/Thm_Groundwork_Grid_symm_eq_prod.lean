-- Prove2me | Theorems.Thm_Groundwork_Grid_symm_eq_prod
-- name    : Groundwork.Grid.symm_eq_prod
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:17:03.27125+00:00
-- url     : https://prove2.me/theorems/ac9580d4-34bb-4501-8a2e-62041ebe28c1
-- title:
--   Grid: symm eq prod
-- statement:
--   The product of all equalities ℓ w w' = ℓ w' w is the product of those inside rows, those inside
--   columns, and of the
--   crossing over the rectangles.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Grid/Grid.lean#L84-L96
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Grid/Grid.lean#L84-L96

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
omit [Fintype α]

theorem Groundwork.Grid.symm_eq_prod (ℓ : Half ρ γ α) : (if ∀ w w', ℓ w w' = ℓ w' w then (1 : ℤ) else 0) =
    (∏ a, ∏ q ∈ pairs γ, if ℓ (a, q.1) (a, q.2) = ℓ (a, q.2) (a, q.1) then 1 else 0) *
    (∏ i, ∏ p ∈ pairs ρ, if ℓ (p.1, i) (p.2, i) = ℓ (p.2, i) (p.1, i) then 1 else 0) *
    ∏ ω ∈ Ω ρ γ, app Cross.X ℓ ω := by sorry
