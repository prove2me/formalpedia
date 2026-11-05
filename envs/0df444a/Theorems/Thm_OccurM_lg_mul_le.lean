-- Prove2me | Theorems.Thm_OccurM_lg_mul_le
-- name    : OccurM.lg_mul_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T04:10:37.322136+00:00
-- url     : https://prove2.me/theorems/bc4e4206-5f0c-47b3-920e-e98ea0a99732
-- title:
--   Occur M: lg mul le
-- statement:
--   log(k·m) ≤ 130·k·m/(log₂(m+2))^α.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/OccurM/ArithBack.lean#L53-L83
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/OccurM/ArithBack.lean#L53-L83

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

theorem OccurM.lg_mul_le (h1 : α ≤ 1) (hk : 1 ≤ k) (hm : 2 ≤ m) : lg ((k : ℝ) * m) ≤ 130 * ((k : ℝ) * m * SatM.rPow α m) := by sorry
