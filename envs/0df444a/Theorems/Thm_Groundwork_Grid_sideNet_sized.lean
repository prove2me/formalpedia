-- Prove2me | Theorems.Thm_Groundwork_Grid_sideNet_sized
-- name    : Groundwork.Grid.sideNet_sized
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:20:54.859041+00:00
-- url     : https://prove2.me/theorems/ffeffa26-c4d7-48d6-a288-cf53ec80e280
-- title:
--   Grid: side Net sized
-- statement:
--   The network before words has size 2g³λ (at most 2^(2g³λ) states and 2g³λ label bits at a node),
--   and values of at most g·B + g²·λ bits.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SideNet.lean#L142-L158
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SideNet.lean#L142-L158

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Math_SideCodes
import Definitions.Def_StepMachines_Math_CodeSeq
import Definitions.Def_StepMachines_Math_Pull
import Definitions.Def_Groundwork_Grid_Size
import Definitions.Def_StepMachines_Math_SideNet
set_option autoImplicit false
section
section
open Groundwork Groundwork.Grid
open Finset
open Groundwork.Prog (digit nRect tb capW priceRow priceCol BoundedInst SideNet)

theorem Groundwork.Grid.sideNet_sized {g n B : ℕ} (tr : Bool) (hn : 1 ≤ n) {R : Inst (Fin g × Fin g) (Bits n)}
    (hR : ∀ w h, |R w h| ≤ 2 ^ B) (y : ℕ) : (sideNet g tr n R y).Sized (2 * g ^ 3 * n) (g * B + g ^ 2 * n) := by sorry
