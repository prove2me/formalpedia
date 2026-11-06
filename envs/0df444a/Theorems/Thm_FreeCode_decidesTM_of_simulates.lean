-- Prove2me | Theorems.Thm_FreeCode_decidesTM_of_simulates
-- name    : FreeCode.decidesTM_of_simulates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:27:18.759201+00:00
-- url     : https://prove2.me/theorems/41019392-ecb4-4808-8450-87312aa05280
-- title:
--   Free Code: decides TM of simulates
-- statement:
--   If Ms decides w-SAT on codes with the exponent δ/2 and the constant c, and the Turing machine M
--   simulates Ms with polynomial overhead, then M decides w-SAT on codes within ⌊C·2^{δn}⌋ steps, for
--   some C ≥ c.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FreeCode/Behind.lean#L78-L109
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FreeCode/Behind.lean#L78-L109

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FreeCode_Defs
import Definitions.Def_FreeCode_Code
import Definitions.Def_SplitSat_Leaf
import Definitions.Def_ToTuring_Machine_EndTM
import Mathlib.Tactic
import Definitions.Def_FreeCode_Behind
set_option autoImplicit false
section
section
open FreeCode
open Groundwork Groundwork.Prog Paper SplitSat

theorem FreeCode.decidesTM_of_simulates {w : ℕ} {δ : ℝ} (hδ : 0 < δ) {Ms : StepMachine (List Bool) Bool} {M : Turing.TM2ComputableAux Bool Bool} {q c : ℕ}
    (hs : Simulates M Ms q) (h : DecidesFree Ms w (δ / 2) c) : ∃ C : ℕ, c ≤ C ∧ SatFree.DecidesTM w M fun n => ⌊(C : ℝ) * (2 : ℝ) ^ (δ * n)⌋₊ := by sorry
