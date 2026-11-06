-- Prove2me | Theorems.Thm_FreeCode_len_stepR_le
-- name    : FreeCode.len_stepR_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:31:40.837983+00:00
-- url     : https://prove2.me/theorems/93a8e4ab-3f29-4f0c-b372-eba57e7f47b8
-- title:
--   Free Code: len step R le
-- statement:
--   One step of the reader makes the word of the state longer by at most 12 symbols.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FreeCode/ReaderCert.lean#L28-L31
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FreeCode/ReaderCert.lean#L28-L31

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FreeCode_Reader
import Definitions.Def_ToTuring_Poly_Decode
import Definitions.Def_ToTuring_Closure_Fold
import Definitions.Def_ToTuring_Lib_Unary
import Mathlib.Tactic
import Definitions.Def_FreeCode_ReaderCert
set_option autoImplicit false
section
section
open FreeCode
open Groundwork Groundwork.Prog Groundwork.Decode

theorem FreeCode.len_stepR_le (w : ℕ) (s : RState) (e : Bool) : len (stepR w s e) ≤ len s + 12 := by sorry
