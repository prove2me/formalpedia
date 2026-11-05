-- Prove2me | Theorems.Thm_Groundwork_DecodeK_length_blk
-- name    : Groundwork.DecodeK.length_blk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:00:30.700194+00:00
-- url     : https://prove2.me/theorems/e9062671-2ab6-4f59-9682-3b25dc62d905
-- title:
--   Decode K: length blk
-- statement:
--   Every clause takes k·(⌊log₂ (2n)⌋ + 1) bits.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/WidthK/Decode.lean#L83-L84
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/WidthK/Decode.lean#L83-L84

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
import Theorems.Thm_Groundwork_Decode_length_blk

set_option autoImplicit false
section
open Groundwork Groundwork.DecodeK
open Sat3 (Lit CNF Satisfiable slot)
open SatK
open Groundwork.Decode

theorem Groundwork.DecodeK.length_blk (k n : ℕ) (C : List (Lit n)) : (blk k n C).length = k * (Nat.log2 (2 * n) + 1) := by sorry
