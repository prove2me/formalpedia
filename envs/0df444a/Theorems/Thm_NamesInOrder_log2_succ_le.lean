-- Prove2me | Theorems.Thm_NamesInOrder_log2_succ_le
-- name    : NamesInOrder.log2_succ_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:28:11.204792+00:00
-- url     : https://prove2.me/theorems/0e15a73d-6811-49f6-9ffa-f40b388d2c40
-- title:
--   Names In Order: log2 succ le
-- statement:
--   ⌊log₂(2n)⌋ + 1 ≤ 2x if n ≤ x and x ≥ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/NamesInOrder/Arith.lean#L54-L61
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/NamesInOrder/Arith.lean#L54-L61

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

theorem NamesInOrder.log2_succ_le {n x : ℕ} (h : n ≤ x) (hx : 1 ≤ x) : Nat.log2 (2 * n) + 1 ≤ 2 * x := by sorry
