-- Prove2me | Theorems.Thm_OccurM_one_le_expClauses
-- name    : OccurM.one_le_expClauses
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:22:29.21021+00:00
-- url     : https://prove2.me/theorems/02671ffe-ac1a-42bb-88a8-a68fe1f0dfa9
-- title:
--   Occur M: one le exp Clauses
-- statement:
--   The printed exponent is at least 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/OccurM/Arith.lean#L68-L75
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/OccurM/Arith.lean#L68-L75

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

theorem OccurM.one_le_expClauses (h0 : 0 ≤ α) (h1 : α ≤ 1) (hk : 1 ≤ k) (hm : 2 ≤ m) : 1 ≤ expClauses α k m := by sorry
