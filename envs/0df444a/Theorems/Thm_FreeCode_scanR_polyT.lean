-- Prove2me | Theorems.Thm_FreeCode_scanR_polyT
-- name    : FreeCode.scanR_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:28:41.624031+00:00
-- url     : https://prove2.me/theorems/8b1992fd-cbdb-412d-8304-7b900f7ec993
-- title:
--   Free Code: scan R poly T
-- statement:
--   Going through all bits is polynomial time.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FreeCode/ReaderCert.lean#L40-L47
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FreeCode/ReaderCert.lean#L40-L47

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

theorem FreeCode.scanR_polyT : PolyT scanR := by sorry
