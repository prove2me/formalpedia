-- Prove2me | Theorems.Thm_Groundwork_Grid_symm_iff
-- name    : Groundwork.Grid.symm_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:16:57.476252+00:00
-- url     : https://prove2.me/theorems/c7cd87ca-c933-4418-819f-2dca63bd3abe
-- title:
--   Grid: symm iff
-- statement:
--   The two copies of every edge agree if and only if they agree on the edges inside rows, on the
--   edges inside columns and on
--   the two diagonals of every rectangle.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Grid/Grid.lean#L52-L78
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Grid/Grid.lean#L52-L78

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
omit [Fintype α] [DecidableEq α]

theorem Groundwork.Grid.symm_iff (ℓ : Half ρ γ α) : (∀ w w', ℓ w w' = ℓ w' w) ↔
    ((∀ a, ∀ q ∈ pairs γ, ℓ (a, q.1) (a, q.2) = ℓ (a, q.2) (a, q.1)) ∧
     (∀ i, ∀ p ∈ pairs ρ, ℓ (p.1, i) (p.2, i) = ℓ (p.2, i) (p.1, i))) ∧
     ∀ ω ∈ Ω ρ γ, ℓ (ω.1.1, ω.2.1) (ω.1.2, ω.2.2) = ℓ (ω.1.2, ω.2.2) (ω.1.1, ω.2.1) ∧
       ℓ (ω.1.1, ω.2.2) (ω.1.2, ω.2.1) = ℓ (ω.1.2, ω.2.1) (ω.1.1, ω.2.2) := by sorry
