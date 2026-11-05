-- Prove2me | Theorems.Thm_OccurM_back_le
-- name    : OccurM.back_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T04:10:31.315978+00:00
-- url     : https://prove2.me/theorems/221e90a7-0189-44bd-99c8-de5b44472011
-- title:
--   Occur M: back le
-- statement:
--   The printed bound with the constant C, plus C·a^C for a number a ≤ 8·(k·m)², is at most the
--   bound `SatM.bound`, with exponent k·m/(log₂(m+2))^α, for the constant 650·C + 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/OccurM/ArithBack.lean#L87-L127
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/OccurM/ArithBack.lean#L87-L127

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClausesOccurStatement
import Definitions.Def_OccurM_Arith
import Definitions.Def_VariableBound_Paper_Arith
import Definitions.Def_Wrap_Arith
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Definitions.Def_OccurM_ArithBack
set_option autoImplicit false
section
section
open OccurM
open MainTheoremForms ClausesOccur VariableBound.Paper
variable {α : ℝ} {k m : ℕ}

theorem OccurM.back_le (h0 : 0 ≤ α) (h1 : α ≤ 1) (C : ℕ) (hk : 1 ≤ k) (hm : 2 ≤ m) {a : ℕ} (ha : a ≤ 8 * (k * m) ^ 2) :
    timeClauses α C k m + C * a ^ C ≤ SatM.bound (SatM.rPow α) (650 * C + 1) k m := by sorry
