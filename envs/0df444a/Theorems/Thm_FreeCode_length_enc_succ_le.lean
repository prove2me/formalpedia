-- Prove2me | Theorems.Thm_FreeCode_length_enc_succ_le
-- name    : FreeCode.length_enc_succ_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:39:08.352183+00:00
-- url     : https://prove2.me/theorems/81e64538-a322-4519-bd30-51d3158c53bc
-- title:
--   Free Code: length enc succ le
-- statement:
--   The length of the code, plus one, of a k-CNF on n variables is at most (2^k·(k+1) + 2)·(n+2)^(k+1).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FreeCode/Code.lean#L98-L114
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FreeCode/Code.lean#L98-L114

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FreeCode_Defs
import Definitions.Def_WidthK_Decode
import Mathlib.Tactic
import Definitions.Def_FreeCode_Code
import Theorems.Thm_Groundwork_DecodeK_length_enc_succ_le
import Theorems.Thm_Groundwork_Decode_length_enc_succ_le
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open FreeCode
open Groundwork Groundwork.Prog Groundwork.Decode
open Sat3 (Lit CNF slot)

theorem FreeCode.length_enc_succ_le {k n : ℕ} {φ : CNF n} (h : SatK.IsKCNF k φ) : (SatFree.enc φ).length + 1 ≤ (2 ^ k * (k + 1) + 2) * (n + 2) ^ (k + 1) := by sorry
