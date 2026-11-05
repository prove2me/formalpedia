-- Prove2me | Theorems.Thm_OccurM_pow_le_timeClauses
-- name    : OccurM.pow_le_timeClauses
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T04:06:12.061209+00:00
-- url     : https://prove2.me/theorems/70ce57cd-9285-45ea-9c23-acdbd36221a7
-- title:
--   Occur M: pow le time Clauses
-- statement:
--   2^e is at most the printed bound with the constant C if e ≤ C·X.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/OccurM/Arith.lean#L129-L134
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/OccurM/Arith.lean#L129-L134

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

theorem OccurM.pow_le_timeClauses {e C : ℕ} (h : (e : ℝ) ≤ C * expClauses α k m) : 2 ^ e ≤ timeClauses α C k m := by sorry
