-- Prove2me | Theorems.Thm_Groundwork_GridArith_size_three_pow_le
-- name    : Groundwork.GridArith.size_three_pow_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:15:20.041571+00:00
-- url     : https://prove2.me/theorems/312e3ab4-a6a8-452a-b2f8-b0c270180f26
-- title:
--   Grid Arith: size three pow le
-- statement:
--   The number 3^c has at most c·log₂3 + 1 bits.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/GridArith.lean#L23-L32
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/GridArith.lean#L23-L32

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_NetworkStatements
import Definitions.Def_StepMachines_Math_GridArith
set_option autoImplicit false
section
section
open Groundwork Groundwork.GridArith

theorem Groundwork.GridArith.size_three_pow_le (c : ℕ) : ((Nat.size (3 ^ c) : ℕ) : ℝ) ≤ c * Real.logb 2 3 + 1 := by sorry
