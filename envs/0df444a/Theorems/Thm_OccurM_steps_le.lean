-- Prove2me | Theorems.Thm_OccurM_steps_le
-- name    : OccurM.steps_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T02:36:53.548768+00:00
-- url     : https://prove2.me/theorems/4a1e3224-bf65-4906-b4e0-3530d2ca928a
-- title:
--   Occur M: steps le
-- statement:
--   q·(a + 2^E + 1)^q, with E ≤ G·X, X ≥ 1 and a ≥ 1, is at most 2^{C·X} + C·a^C with C =
--   `stepsC q G`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/OccurM/Arith.lean#L175-L191
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/OccurM/Arith.lean#L175-L191

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

theorem OccurM.steps_le (q G : ℕ) {E a : ℕ} (hE : (E : ℝ) ≤ G * expClauses α k m) (hX : 1 ≤ expClauses α k m) (ha : 1 ≤ a) :
    q * (a + 2 ^ E + 1) ^ q ≤ timeClauses α (stepsC q G) k m + stepsC q G * a ^ stepsC q G := by sorry
