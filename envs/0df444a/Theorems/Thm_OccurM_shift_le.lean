-- Prove2me | Theorems.Thm_OccurM_shift_le
-- name    : OccurM.shift_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:38:10.930021+00:00
-- url     : https://prove2.me/theorems/f9fcf3d5-8077-4d3c-9a2e-e54732b3ba3f
-- title:
--   Occur M: shift le
-- statement:
--   k·m/(log₂(m+2))^α ≤ k·m/(log m)^α.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/OccurM/Arith.lean#L78-L85
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/OccurM/Arith.lean#L78-L85

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

theorem OccurM.shift_le (h0 : 0 ≤ α) (k : ℕ) (hm : 2 ≤ m) : (k : ℝ) * m * SatM.rPow α m ≤ expClauses α k m := by sorry
