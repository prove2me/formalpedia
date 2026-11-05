-- Prove2me | Theorems.Thm_Groundwork_Decode_length_body
-- name    : Groundwork.Decode.length_body
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:33:03.906207+00:00
-- url     : https://prove2.me/theorems/e044389f-824f-4b0e-b90c-fc7ae9226184
-- title:
--   Decode: length body
-- statement:
--   The Decode construction uses the length body property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Decode.lean#L143-L146
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Decode.lean#L143-L146

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

theorem Groundwork.Decode.length_body {n : ℕ} (φ : CNF n) : (φ.map (blk n)).flatten.length = φ.length * (3 * (Nat.log2 (2 * n) + 1)) := by sorry
