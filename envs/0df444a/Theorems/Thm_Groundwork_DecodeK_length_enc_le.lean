-- Prove2me | Theorems.Thm_Groundwork_DecodeK_length_enc_le
-- name    : Groundwork.DecodeK.length_enc_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:23:43.786095+00:00
-- url     : https://prove2.me/theorems/0976c702-1903-400c-9dd2-67442a5add27
-- title:
--   Decode K: length enc le
-- statement:
--   The code of an instance of k-SAT has at most n + 1 + k·(⌊log₂ (2n)⌋ + 1)·(2n+1)^k bits.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/WidthK/Decode.lean#L133-L136
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/WidthK/Decode.lean#L133-L136

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
import Theorems.Thm_Groundwork_Decode_length_enc_le

set_option autoImplicit false
section
open Groundwork Groundwork.DecodeK
open Sat3 (Lit CNF Satisfiable slot)
open SatK
open Groundwork.Decode

theorem Groundwork.DecodeK.length_enc_le {k n : ℕ} {φ : CNF n} (h : IsKCNF k φ) :
    (enc k φ).length ≤ n + 1 + k * (Nat.log2 (2 * n) + 1) * (2 * n + 1) ^ k := by sorry
