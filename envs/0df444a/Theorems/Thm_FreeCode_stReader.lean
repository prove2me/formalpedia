-- Prove2me | Theorems.Thm_FreeCode_stReader
-- name    : FreeCode.stReader
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:28:44.583197+00:00
-- url     : https://prove2.me/theorems/fcf88608-3cab-4f19-a382-0534c44a9e39
-- title:
--   Free Code: st Reader
-- statement:
--   There is a polynomial-time reader: the statement `FreeCode.StReader`. The reader is `readFree`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FreeCode/ReaderCert.lean#L58-L58
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FreeCode/ReaderCert.lean#L58-L58

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

theorem FreeCode.stReader : StReader := by sorry
