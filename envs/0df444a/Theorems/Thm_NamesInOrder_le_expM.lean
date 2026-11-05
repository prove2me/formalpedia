-- Prove2me | Theorems.Thm_NamesInOrder_le_expM
-- name    : NamesInOrder.le_expM
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:15:46.647575+00:00
-- url     : https://prove2.me/theorems/f6af590f-76a2-4e26-adb1-9e449b6f4113
-- title:
--   Names In Order: le exp M
-- statement:
--   k ≤ km/√(log m) and log m ≤ km/√(log m), for k ≥ 1 and m ≥ 2.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/NamesInOrder/Arith.lean#L123-L130
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/NamesInOrder/Arith.lean#L123-L130

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

theorem NamesInOrder.le_expM {k m : ℕ} (hk : 1 ≤ k) (hm : 2 ≤ m) : (k : ℝ) ≤ expM k m ∧ lg m ≤ expM k m := by sorry
