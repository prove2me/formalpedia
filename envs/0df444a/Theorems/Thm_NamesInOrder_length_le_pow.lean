-- Prove2me | Theorems.Thm_NamesInOrder_length_le_pow
-- name    : NamesInOrder.length_le_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:13:41.134918+00:00
-- url     : https://prove2.me/theorems/8b5e17c4-035d-405f-9f0c-31873847c2f5
-- title:
--   Names In Order: length le pow
-- statement:
--   As no clause is repeated, the input has at most k·(2n+1)^(k+3) bits (k ≥ 1, n ≥ 1).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/NamesInOrder/Arith.lean#L78-L96
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/NamesInOrder/Arith.lean#L78-L96

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
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open NamesInOrder
open Turing MainTheoremForms VariableBound.Paper MinOfBounds PairsToBound
open Sat3 (CNF)

theorem NamesInOrder.length_le_pow {k n : ℕ} {φ : CNF n} (hk : 1 ≤ k) (hn : 1 ≤ n) (hφ : SatK.IsKCNF k φ) : (SatM.enc k φ).length ≤ k * (2 * n + 1) ^ (k + 3) := by sorry
