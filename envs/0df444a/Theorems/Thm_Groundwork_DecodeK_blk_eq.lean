-- Prove2me | Theorems.Thm_Groundwork_DecodeK_blk_eq
-- name    : Groundwork.DecodeK.blk_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:23:41.293793+00:00
-- url     : https://prove2.me/theorems/0a0a672e-32e9-40d9-9d65-76fc32993b96
-- title:
--   Decode K: blk eq
-- statement:
--   The bits of a clause are the words of its k slots, laid end to end.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/WidthK/Decode.lean#L78-L80
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/WidthK/Decode.lean#L78-L80

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_KSatStatement
import Definitions.Def_StepMachines_Prog_Decode
import Definitions.Def_StepMachines_Prog_Decode
import Definitions.Def_StepMachines_Prog_Decode
import Definitions.Def_StepMachines_Math_Formula
import Definitions.Def_StepMachines_Math_Formula
import Definitions.Def_WidthK_Decode
import Theorems.Thm_Groundwork_Decode_blk_eq

set_option autoImplicit false
section
open Groundwork Groundwork.DecodeK
open Sat3 (Lit CNF Satisfiable slot)
open SatK
open Groundwork.Decode

theorem Groundwork.DecodeK.blk_eq (k n : ℕ) (C : List (Lit n)) : blk k n C =
    ((List.range k).map fun j => toWord (Nat.log2 (2 * n) + 1) (slot C[j]?)).flatten := by sorry
