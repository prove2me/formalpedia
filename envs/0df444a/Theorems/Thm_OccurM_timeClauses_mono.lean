-- Prove2me | Theorems.Thm_OccurM_timeClauses_mono
-- name    : OccurM.timeClauses_mono
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T04:07:36.846994+00:00
-- url     : https://prove2.me/theorems/7054f39b-5c85-4110-8c00-1fcf556eb671
-- title:
--   Occur M: time Clauses mono
-- statement:
--   The printed bound grows with the constant.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/OccurM/Arith.lean#L137-L139
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/OccurM/Arith.lean#L137-L139

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

theorem OccurM.timeClauses_mono {C C' : ℕ} (h : C ≤ C') (hX : 0 ≤ expClauses α k m) : timeClauses α C k m ≤ timeClauses α C' k m := by sorry
