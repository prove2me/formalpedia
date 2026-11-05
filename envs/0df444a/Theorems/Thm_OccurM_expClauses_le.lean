-- Prove2me | Theorems.Thm_OccurM_expClauses_le
-- name    : OccurM.expClauses_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T04:09:06.896789+00:00
-- url     : https://prove2.me/theorems/4de727b8-6459-4ae7-9b24-12740b64cbdc
-- title:
--   Occur M: exp Clauses le
-- statement:
--   k·m/(log m)^α ≤ 2·k·m/(log₂(m+2))^α.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/OccurM/Arith.lean#L110-L124
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/OccurM/Arith.lean#L110-L124

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

theorem OccurM.expClauses_le (h0 : 0 ≤ α) (h1 : α ≤ 1) (k : ℕ) (hm : 2 ≤ m) : expClauses α k m ≤ 2 * ((k : ℝ) * m * SatM.rPow α m) := by sorry
