-- Prove2me | Theorems.Thm_Groundwork_GridArith_four_mul_choose_sq_le
-- name    : Groundwork.GridArith.four_mul_choose_sq_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:42:20.479077+00:00
-- url     : https://prove2.me/theorems/38a8e40a-d785-45be-8465-e3f456587748
-- title:
--   Grid Arith: four mul choose sq le
-- statement:
--   4·C(g,2)² ≤ g⁴.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/GridArith.lean#L54-L62
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/GridArith.lean#L54-L62

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_NetworkStatements
import Definitions.Def_StepMachines_Math_GridArith
set_option autoImplicit false
section
section
open Groundwork Groundwork.GridArith

theorem Groundwork.GridArith.four_mul_choose_sq_le (g : ℕ) : 4 * g.choose 2 ^ 2 ≤ g ^ 4 := by sorry
