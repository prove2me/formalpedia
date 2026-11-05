-- Prove2me | Theorems.Thm_Groundwork_Decode_mem_toN
-- name    : Groundwork.Decode.mem_toN
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:23:18.171271+00:00
-- url     : https://prove2.me/theorems/b41ba044-b8ed-4dfc-9aa4-a08735c35905
-- title:
--   Decode: mem to N
-- statement:
--   Clauses keep their lengths, and the variables are below `n`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Decode.lean#L209-L214
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Decode.lean#L209-L214

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThreeSatStatement
import Definitions.Def_StepMachines_Prog_Chunks
import Mathlib.Data.Nat.Size
import Definitions.Def_StepMachines_Math_Formula
import Definitions.Def_StepMachines_Prog_Decode
set_option autoImplicit false
section
open Groundwork Groundwork.Decode
open Sat3

theorem Groundwork.Decode.mem_toN {n : ℕ} {φ : CNF n} {D : List (ℕ × Bool)} (hD : D ∈ toN φ) :
    (∃ C ∈ φ, D.length = C.length) ∧ ∀ l ∈ D, l.1 < n := by sorry
