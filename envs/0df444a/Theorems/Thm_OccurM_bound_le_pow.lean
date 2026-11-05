-- Prove2me | Theorems.Thm_OccurM_bound_le_pow
-- name    : OccurM.bound_le_pow
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T04:07:25.05066+00:00
-- url     : https://prove2.me/theorems/1ab2bf0e-5764-489a-b5bd-8f6454ece1f3
-- title:
--   Occur M: bound le pow
-- statement:
--   The bound `SatM.bound` with the constant C is at most 2^E for a natural number E ≤ (2C+1)·X: the
--   factor in front goes into the exponent.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/OccurM/Arith.lean#L143-L166
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/OccurM/Arith.lean#L143-L166

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClausesOccurStatement
import Definitions.Def_VariableBound_Paper_Arith
import Definitions.Def_VariableBound_Paper_Rename_Time
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Definitions.Def_OccurM_Arith
set_option autoImplicit false
section
section
open OccurM
open MainTheoremForms ClausesOccur VariableBound.Paper
variable {α : ℝ} {k m : ℕ}

theorem OccurM.bound_le_pow (h0 : 0 ≤ α) (h1 : α ≤ 1) (C : ℕ) (hk : 1 ≤ k) (hm : 2 ≤ m) :
    ∃ E : ℕ, SatM.bound (SatM.rPow α) C k m ≤ 2 ^ E ∧ (E : ℝ) ≤ ((2 * C + 1 : ℕ) : ℝ) * expClauses α k m := by sorry
