-- Prove2me | Theorems.Thm_OccurM_sq_lg_add_two_le
-- name    : OccurM.sq_lg_add_two_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T04:10:23.781271+00:00
-- url     : https://prove2.me/theorems/01c36bcc-e22b-48e9-afd0-b8e2048e2078
-- title:
--   Occur M: sq lg add two le
-- statement:
--   (log₂(m+2))² ≤ 128·m for m ≥ 2.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/OccurM/ArithBack.lean#L41-L50
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/OccurM/ArithBack.lean#L41-L50

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

theorem OccurM.sq_lg_add_two_le (hm : 2 ≤ m) : lg ((m : ℝ) + 2) * lg ((m : ℝ) + 2) ≤ 128 * m := by sorry
