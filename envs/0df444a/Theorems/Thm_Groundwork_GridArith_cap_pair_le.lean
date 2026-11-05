-- Prove2me | Theorems.Thm_Groundwork_GridArith_cap_pair_le
-- name    : Groundwork.GridArith.cap_pair_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:15:17.1662+00:00
-- url     : https://prove2.me/theorems/c0ff5e0c-9b2f-407a-ab83-1483bbcf24f9
-- title:
--   Grid Arith: cap pair le
-- statement:
--   The two names of a term, with n = λ and d = i: the name for rows has n + size(3^(n−d)) bits, the
--   name for columns n + size(3^d) bits; together they have at most 4ρλ + 2 bits.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/GridArith.lean#L44-L51
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/GridArith.lean#L44-L51

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_NetworkStatements
import Definitions.Def_StepMachines_Math_GridArith
set_option autoImplicit false
section
section
open Groundwork Groundwork.GridArith

theorem Groundwork.GridArith.cap_pair_le {n d : ℕ} (h : d ≤ n) :
    ((n + Nat.size (3 ^ (n - d)) + (n + Nat.size (3 ^ d)) : ℕ) : ℝ) ≤ 4 * ρ * n + 2 := by sorry
