-- Prove2me | Theorems.Thm_FreeCode_scanR_enc_append
-- name    : FreeCode.scanR_enc_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:28:45.9357+00:00
-- url     : https://prove2.me/theorems/a5470b1e-4c37-4b27-9915-e8413b682526
-- title:
--   Free Code: scan R enc append
-- statement:
--   The state of the reader after the code of φ followed by any bits u.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FreeCode/Reader.lean#L135-L141
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FreeCode/Reader.lean#L135-L141

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FreeCode_Defs
import Definitions.Def_FreeCode_Code
import Mathlib.Tactic
import Definitions.Def_FreeCode_Reader
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
section
open FreeCode
open Groundwork Groundwork.Prog Groundwork.Decode
open Sat3 (Lit CNF slot)

theorem FreeCode.scanR_enc_append {n : ℕ} (φ : CNF n) (u : List Bool) :
    scanR (SatFree.enc φ ++ u) = (true, true, [], [], (φ.map fun C => (C.map fun l => (SatFree.encLit l).reverse).reverse).reverse) := by sorry
