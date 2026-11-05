-- Prove2me | Theorems.Thm_Groundwork_length_chunkAt
-- name    : Groundwork.length_chunkAt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:38:47.669433+00:00
-- url     : https://prove2.me/theorems/fc33b2b7-7207-4505-a509-4f8758894b01
-- title:
--   Groundwork: length chunk At
-- statement:
--   The length of a chunk of a word of the full length.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/CodeSeq.lean#L127-L133
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/CodeSeq.lean#L127-L133

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Math_CodeMore
import Definitions.Def_StepMachines_Math_CodeSeq
set_option autoImplicit false
section
open Groundwork
open Finset
variable {X : Type*}

theorem Groundwork.length_chunkAt (n : ℕ → ℕ) {r κ : ℕ} (hκ : κ < r) {w : List Bool} (hw : w.length = ∑ κ' ∈ range r, n κ') :
    (chunkAt n κ w).length = n κ := by sorry
