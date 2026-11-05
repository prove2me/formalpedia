-- Prove2me | Theorems.Thm_Groundwork_DecodeK_length_body
-- name    : Groundwork.DecodeK.length_body
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:00:28.288991+00:00
-- url     : https://prove2.me/theorems/52af879d-b116-4d6b-9a43-6ea7ccec249c
-- title:
--   Decode K: length body
-- statement:
--   The number of bits after the header.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/WidthK/Decode.lean#L103-L107
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/WidthK/Decode.lean#L103-L107

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
import Theorems.Thm_Groundwork_Decode_length_body

set_option autoImplicit false
section
open Groundwork Groundwork.DecodeK
open Sat3 (Lit CNF Satisfiable slot)
open SatK
open Groundwork.Decode

theorem Groundwork.DecodeK.length_body (k : ℕ) {n : ℕ} (φ : CNF n) :
    (φ.map (blk k n)).flatten.length = φ.length * (k * (Nat.log2 (2 * n) + 1)) := by sorry
