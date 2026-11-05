-- Prove2me | Theorems.Thm_Groundwork_DecodeK_clauseDec_blk
-- name    : Groundwork.DecodeK.clauseDec_blk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:23:43.244021+00:00
-- url     : https://prove2.me/theorems/7b62a2b9-3044-4f41-8e29-c7765ba321ba
-- title:
--   Decode K: clause Dec blk
-- statement:
--   Reading the bits of a clause of at most k literals gives the clause back, with its variables as
--   natural numbers.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/WidthK/Decode.lean#L88-L95
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/WidthK/Decode.lean#L88-L95

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
import Theorems.Thm_Groundwork_Decode_clauseDec_blk

set_option autoImplicit false
section
open Groundwork Groundwork.DecodeK
open Sat3 (Lit CNF Satisfiable slot)
open SatK
open Groundwork.Decode

theorem Groundwork.DecodeK.clauseDec_blk {k n : ℕ} {C : List (Lit n)} (hC : C.length ≤ k) :
    clauseDec k (Nat.log2 (2 * n) + 1) (blk k n C) = C.map fun l => (l.1.val, l.2) := by sorry
