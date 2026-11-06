-- Prove2me | Theorems.Thm_FreeCode_stepR_polyT
-- name    : FreeCode.stepR_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:29:05.488106+00:00
-- url     : https://prove2.me/theorems/6ab92a34-16de-46b6-8c6c-1683e3db4175
-- title:
--   Free Code: step R poly T
-- statement:
--   One step of the reader is polynomial time, with the number of bits of a literal as a part of the
--   input.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FreeCode/ReaderCert.lean#L35-L37
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FreeCode/ReaderCert.lean#L35-L37

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

theorem FreeCode.stepR_polyT : PolyT fun p : ℕ × RState × Bool => stepR p.1 p.2.1 p.2.2 := by sorry
