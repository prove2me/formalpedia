-- Prove2me | Theorems.Thm_Groundwork_Decode_bitLen_le
-- name    : Groundwork.Decode.bitLen_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:38:18.208444+00:00
-- url     : https://prove2.me/theorems/046cf0dc-077a-4fc9-945e-bed8d379855f
-- title:
--   Decode: bit Len le
-- statement:
--   The Decode construction uses the bit Len le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Decode.lean#L171-L177
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Decode.lean#L171-L177

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

theorem Groundwork.Decode.bitLen_le (n : ℕ) : (Nat.log2 (2 * n) + 1) ≤ n + 1 := by sorry
