-- Prove2me | Theorems.Thm_Groundwork_exists_pow_le
-- name    : Groundwork.exists_pow_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:48:13.539862+00:00
-- url     : https://prove2.me/theorems/5c241904-c40b-4e67-8048-2a4e49591316
-- title:
--   Groundwork: exists pow le
-- statement:
--   A polynomial is below every exponential, up to a constant.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Machine/EndTM.lean#L32-L47
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Machine/EndTM.lean#L32-L47

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThreeSatStatement
import Definitions.Def_ToTuring_PolyT
import Definitions.Def_ToTuring_Machine_Host
import Definitions.Def_StepMachines_Prog_Decode
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Definitions.Def_ToTuring_Machine_EndTM
set_option autoImplicit false
section
open Groundwork
open Sat3 Turing
open scoped NNReal

theorem Groundwork.exists_pow_le (k : ℕ) {ε : ℝ} (hε : 0 < ε) : ∃ C : ℕ, ∀ n : ℕ, ((n : ℝ) + 2) ^ k ≤ C * (2 : ℝ) ^ (ε * n) := by sorry
