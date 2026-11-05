-- Prove2me | Theorems.Thm_OccurM_lg_add_two_le
-- name    : OccurM.lg_add_two_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:36:35.150991+00:00
-- url     : https://prove2.me/theorems/703bce3c-9580-4f70-bdfb-583a0f139b5a
-- title:
--   Occur M: lg add two le
-- statement:
--   log₂(m+2) ≤ 2·log m, since m + 2 ≤ m².
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/OccurM/Arith.lean#L88-L95
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/OccurM/Arith.lean#L88-L95

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

theorem OccurM.lg_add_two_le (hm : 2 ≤ m) : lg ((m : ℝ) + 2) ≤ 2 * lg m := by sorry
