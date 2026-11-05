-- Prove2me | Theorems.Thm_Groundwork_DecodeK_length_enc
-- name    : Groundwork.DecodeK.length_enc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:43:40.335905+00:00
-- url     : https://prove2.me/theorems/0a98cc96-f3d3-4498-a5ea-2e708d26ddf2
-- title:
--   Decode K: length enc
-- statement:
--   The exact length of the code: the header, then k slots for every clause.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/WidthK/Decode.lean#L128-L130
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/WidthK/Decode.lean#L128-L130

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
import Theorems.Thm_Groundwork_Decode_length_enc

set_option autoImplicit false
section
open Groundwork Groundwork.DecodeK
open Sat3 (Lit CNF Satisfiable slot)
open SatK
open Groundwork.Decode

theorem Groundwork.DecodeK.length_enc (k : ℕ) {n : ℕ} (φ : CNF n) :
    (enc k φ).length = n + 1 + φ.length * (k * (Nat.log2 (2 * n) + 1)) := by sorry
