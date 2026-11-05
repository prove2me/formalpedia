-- Prove2me | Theorems.Thm_NamesInOrder_pow_le_two_rpow
-- name    : NamesInOrder.pow_le_two_rpow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:15:47.175319+00:00
-- url     : https://prove2.me/theorems/3768ed1b-6508-413e-b887-6c1c27c9b34b
-- title:
--   Names In Order: pow le two rpow
-- statement:
--   k·(2n+1)^(k+3) ≤ 2^{9Y}, Y = k²·n·log log n/√(log n), for k ≥ 1 and n ≥ 4.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/NamesInOrder/Arith.lean#L160-L178
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/NamesInOrder/Arith.lean#L160-L178

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
import Theorems.Thm_Groundwork_SatNet_pow_le_two_rpow

set_option autoImplicit false
section
section
open NamesInOrder
open Turing MainTheoremForms VariableBound.Paper MinOfBounds PairsToBound
open Sat3 (CNF)

theorem NamesInOrder.pow_le_two_rpow {k n : ℕ} (hk : 1 ≤ k) (hn : 4 ≤ n) : ((k * (2 * n + 1) ^ (k + 3) : ℕ) : ℝ) ≤ (2 : ℝ) ^ (((9 : ℕ) : ℝ) * expN k n) := by sorry
