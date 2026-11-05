-- Prove2me | Theorems.Thm_Groundwork_Decode_block_flatten
-- name    : Groundwork.Decode.block_flatten
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:30:43.726851+00:00
-- url     : https://prove2.me/theorems/2e64c91c-696f-4b6c-a1f3-605ed62f37e5
-- title:
--   Decode: block flatten
-- statement:
--   Blocks of one length, laid end to end, are read back by offset.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Decode.lean#L85-L96
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Decode.lean#L85-L96

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

theorem Groundwork.Decode.block_flatten {w : ℕ} : ∀ {L : List (List Bool)} (_ : ∀ l ∈ L, l.length = w) (i : ℕ) (hi : i < L.length),
    block w i L.flatten = L[i]
  := by sorry
