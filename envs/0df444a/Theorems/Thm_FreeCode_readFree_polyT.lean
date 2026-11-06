-- Prove2me | Theorems.Thm_FreeCode_readFree_polyT
-- name    : FreeCode.readFree_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:59:03.286436+00:00
-- url     : https://prove2.me/theorems/f95cadbd-f7eb-48ea-8eb5-be9e0600f947
-- title:
--   Free Code: read Free poly T
-- statement:
--   The reader is polynomial time.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FreeCode/ReaderCert.lean#L50-L55
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FreeCode/ReaderCert.lean#L50-L55

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

theorem FreeCode.readFree_polyT : PolyT readFree := by sorry
