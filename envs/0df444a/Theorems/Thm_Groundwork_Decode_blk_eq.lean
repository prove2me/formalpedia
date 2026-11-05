-- Prove2me | Theorems.Thm_Groundwork_Decode_blk_eq
-- name    : Groundwork.Decode.blk_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:38:15.495341+00:00
-- url     : https://prove2.me/theorems/23dd2f8b-4214-42df-8f89-1f3c9591e857
-- title:
--   Decode: blk eq
-- statement:
--   The Decode construction uses the blk eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Decode.lean#L102-L105
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Decode.lean#L102-L105

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

theorem Groundwork.Decode.blk_eq (n : ℕ) (C : List (Lit n)) : blk n C =
    [toWord ((Nat.log2 (2 * n) + 1)) (slot C[0]?), toWord ((Nat.log2 (2 * n) + 1)) (slot C[1]?),
      toWord ((Nat.log2 (2 * n) + 1)) (slot C[2]?)].flatten := by sorry
