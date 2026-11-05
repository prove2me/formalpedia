-- Prove2me | Theorems.Thm_Groundwork_SatNet_pow_le_two_rpow
-- name    : Groundwork.SatNet.pow_le_two_rpow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:39:00.839455+00:00
-- url     : https://prove2.me/theorems/fee3c913-ff9f-4f4f-a563-4edc5d57d0a4
-- title:
--   Sat Net: pow le two rpow
-- statement:
--   A power is below an exponential.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SatArith.lean#L20-L30
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SatArith.lean#L20-L30

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_StepMachines_Math_SatArith
set_option autoImplicit false
section
open Groundwork Groundwork.SatNet

theorem Groundwork.SatNet.pow_le_two_rpow (A : ℕ) {c : ℝ} (hc : 0 < c) : ∃ C : ℕ, ∀ x : ℕ, (x : ℝ) ^ A ≤ C * (2 : ℝ) ^ (c * x) := by sorry
