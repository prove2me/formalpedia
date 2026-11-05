-- Prove2me | Theorems.Thm_OccurM_lg_add_two_rpow_le
-- name    : OccurM.lg_add_two_rpow_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T04:08:54.423204+00:00
-- url     : https://prove2.me/theorems/6ee280d0-03d3-41fa-8c54-8df1ab42c8b7
-- title:
--   Occur M: lg add two rpow le
-- statement:
--   (log₂(m+2))^α ≤ 2·(log m)^α.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/OccurM/Arith.lean#L98-L107
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/OccurM/Arith.lean#L98-L107

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

theorem OccurM.lg_add_two_rpow_le (h0 : 0 ≤ α) (h1 : α ≤ 1) (hm : 2 ≤ m) : lg ((m : ℝ) + 2) ^ α ≤ 2 * lg m ^ α := by sorry
