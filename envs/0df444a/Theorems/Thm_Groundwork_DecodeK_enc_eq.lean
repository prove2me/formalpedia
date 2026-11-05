-- Prove2me | Theorems.Thm_Groundwork_DecodeK_enc_eq
-- name    : Groundwork.DecodeK.enc_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:00:32.882209+00:00
-- url     : https://prove2.me/theorems/0d2d05a3-c19b-4650-9ae9-eb4aaddae612
-- title:
--   Decode K: enc eq
-- statement:
--   The code is the header 1ⁿ 0 followed by the bits of the clauses.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/WidthK/Decode.lean#L98-L100
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/WidthK/Decode.lean#L98-L100

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
import Theorems.Thm_Groundwork_Decode_enc_eq

set_option autoImplicit false
section
open Groundwork Groundwork.DecodeK
open Sat3 (Lit CNF Satisfiable slot)
open SatK
open Groundwork.Decode

theorem Groundwork.DecodeK.enc_eq (k : ℕ) {n : ℕ} (φ : CNF n) : enc k φ = List.replicate n true ++ false :: (φ.map (blk k n)).flatten := by sorry
