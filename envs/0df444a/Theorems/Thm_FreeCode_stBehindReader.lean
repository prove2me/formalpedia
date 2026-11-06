-- Prove2me | Theorems.Thm_FreeCode_stBehindReader
-- name    : FreeCode.stBehindReader
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:45:28.391396+00:00
-- url     : https://prove2.me/theorems/d15ec133-7017-452f-b43e-82209e92f6f1
-- title:
--   Free Code: st Behind Reader
-- statement:
--   **For every reader and every procedure D** that decides w-SAT on (N in unary, formula) with the
--   exponent δ: D behind the reader decides w-SAT on the code, within the same number of steps. This is
--   the statement `FreeCode.StBehindReader`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FreeCode/Behind.lean#L35-L41
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FreeCode/Behind.lean#L35-L41

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FreeCode_Defs
import Definitions.Def_FreeCode_Code
import Definitions.Def_SplitSat_Leaf
import Definitions.Def_ToTuring_Machine_EndTM
import Mathlib.Tactic
import Definitions.Def_FreeCode_Behind
set_option autoImplicit false
section
section
open FreeCode
open Groundwork Groundwork.Prog Paper SplitSat

theorem FreeCode.stBehindReader : StBehindReader := by sorry
