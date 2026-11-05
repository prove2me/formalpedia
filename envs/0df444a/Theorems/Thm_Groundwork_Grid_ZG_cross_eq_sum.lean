-- Prove2me | Theorems.Thm_Groundwork_Grid_ZG_cross_eq_sum
-- name    : Groundwork.Grid.ZG_cross_eq_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:17:27.932416+00:00
-- url     : https://prove2.me/theorems/1d8df57e-e269-466d-8509-e42a8cfccd20
-- title:
--   Grid: ZG cross eq sum
-- statement:
--   The value with the crossing `Cross.X` on every rectangle is the sum over ι of the terms Z_ι.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Grid/Expand.lean#L49-L59
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Grid/Expand.lean#L49-L59

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Grid_RowNet
import Definitions.Def_Groundwork_Cross_Bit
import Definitions.Def_Groundwork_Grid_Expand
set_option autoImplicit false
section
section
open Groundwork Groundwork.Grid
open Finset
variable {ρ γ α : Type}
variable [Fintype ρ] [LinearOrder ρ] [Fintype γ] [LinearOrder γ]

theorem Groundwork.Grid.ZG_cross_eq_sum {n : ℕ} (R : Inst (ρ × γ) (Bits n)) :
    ZG R (fun _ => Cross.X) = ∑ ι ∈ Pat ρ γ n, ZG R fun ω => A n (ι ω) := by sorry
