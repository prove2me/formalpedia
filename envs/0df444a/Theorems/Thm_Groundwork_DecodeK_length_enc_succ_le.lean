-- Prove2me | Theorems.Thm_Groundwork_DecodeK_length_enc_succ_le
-- name    : Groundwork.DecodeK.length_enc_succ_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:56:56.176577+00:00
-- url     : https://prove2.me/theorems/51bff0c5-73a7-4d6d-aa88-11ddcfa8b4e6
-- title:
--   Decode K: length enc succ le
-- statement:
--   The length of the code of an instance of k-SAT, plus one, is at most (k·2^k + 1)·(n+2)^(k+1):
--   polynomial in n for fixed k.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/WidthK/Decode.lean#L140-L148
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/WidthK/Decode.lean#L140-L148

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
import Theorems.Thm_Groundwork_Decode_length_enc_succ_le

set_option autoImplicit false
section
open Groundwork Groundwork.DecodeK
open Sat3 (Lit CNF Satisfiable slot)
open SatK
open Groundwork.Decode

theorem Groundwork.DecodeK.length_enc_succ_le {k n : ℕ} {φ : CNF n} (h : IsKCNF k φ) :
    (enc k φ).length + 1 ≤ (k * 2 ^ k + 1) * (n + 2) ^ (k + 1) := by sorry
