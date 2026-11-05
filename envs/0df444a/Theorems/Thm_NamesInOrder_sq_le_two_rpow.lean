-- Prove2me | Theorems.Thm_NamesInOrder_sq_le_two_rpow
-- name    : NamesInOrder.sq_le_two_rpow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:16:07.96042+00:00
-- url     : https://prove2.me/theorems/a1fd4269-2805-4cb8-9b2b-06f85093dac5
-- title:
--   Names In Order: sq le two rpow
-- statement:
--   6·(km)² ≤ 2^{6X}, X = km/√(log m), for k ≥ 1 and m ≥ 2.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/NamesInOrder/Arith.lean#L133-L157
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/NamesInOrder/Arith.lean#L133-L157

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_NamesInOrder_Defs
import Definitions.Def_MinOfBounds_Arith
import Definitions.Def_PairsToBound_Arith
import Definitions.Def_VariableBound_Paper_Arith
import Definitions.Def_VariableBound_Paper_Forms
import Definitions.Def_ClauseBound_Alg_End
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Definitions.Def_NamesInOrder_Arith
set_option autoImplicit false
section
section
open NamesInOrder
open Turing MainTheoremForms VariableBound.Paper MinOfBounds PairsToBound
open Sat3 (CNF)

theorem NamesInOrder.sq_le_two_rpow {k m : ℕ} (hk : 1 ≤ k) (hm : 2 ≤ m) : ((6 * (k * m) ^ 2 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (((6 : ℕ) : ℝ) * expM k m) := by sorry
