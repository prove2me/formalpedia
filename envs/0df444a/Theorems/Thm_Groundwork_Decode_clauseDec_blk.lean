-- Prove2me | Theorems.Thm_Groundwork_Decode_clauseDec_blk
-- name    : Groundwork.Decode.clauseDec_blk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:41:39.383194+00:00
-- url     : https://prove2.me/theorems/636ecb4e-b7d9-48c0-ad35-05e47738e544
-- title:
--   Decode: clause Dec blk
-- statement:
--   The Decode construction uses the clause Dec blk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Decode.lean#L110-L125
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Decode.lean#L110-L125

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

theorem Groundwork.Decode.clauseDec_blk {n : ℕ} {C : List (Lit n)} (hC : C.length ≤ 3) :
    clauseDec ((Nat.log2 (2 * n) + 1)) (blk n C) = C.map fun l => (l.1.val, l.2) := by sorry
