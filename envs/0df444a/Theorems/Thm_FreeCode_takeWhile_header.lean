-- Prove2me | Theorems.Thm_FreeCode_takeWhile_header
-- name    : FreeCode.takeWhile_header
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:46:03.157634+00:00
-- url     : https://prove2.me/theorems/536c7a65-c7f5-4f09-875a-a5d7c06241a6
-- title:
--   Free Code: take While header
-- statement:
--   The ones in front of the first zero.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FreeCode/Reader.lean#L64-L67
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FreeCode/Reader.lean#L64-L67

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FreeCode_Defs
import Definitions.Def_FreeCode_Code
import Mathlib.Tactic
import Definitions.Def_FreeCode_Reader
import Theorems.Thm_Groundwork_Decode_takeWhile_header
import Theorems.Thm_Groundwork_PolyT_takeWhile
attribute [local fun_prop] Groundwork.PolyT.takeWhile


set_option autoImplicit false
section
section
section
open FreeCode
open Groundwork Groundwork.Prog Groundwork.Decode
open Sat3 (Lit CNF slot)

theorem FreeCode.takeWhile_header (n : ℕ) (l : List Bool) : (List.replicate n true ++ false :: l).takeWhile id = List.replicate n true := by sorry
