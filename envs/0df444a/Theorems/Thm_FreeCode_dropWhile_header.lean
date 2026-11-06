-- Prove2me | Theorems.Thm_FreeCode_dropWhile_header
-- name    : FreeCode.dropWhile_header
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:27:35.819592+00:00
-- url     : https://prove2.me/theorems/ed310458-d75b-4b24-aab9-784c34bb3d13
-- title:
--   Free Code: drop While header
-- statement:
--   What stands from the first zero on.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FreeCode/Reader.lean#L70-L73
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FreeCode/Reader.lean#L70-L73

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FreeCode_Defs
import Definitions.Def_FreeCode_Code
import Mathlib.Tactic
import Definitions.Def_FreeCode_Reader
import Theorems.Thm_Groundwork_Decode_dropWhile_header
import Theorems.Thm_Groundwork_PolyT_dropWhile
attribute [local fun_prop] Groundwork.PolyT.dropWhile


set_option autoImplicit false
section
section
section
open FreeCode
open Groundwork Groundwork.Prog Groundwork.Decode
open Sat3 (Lit CNF slot)

theorem FreeCode.dropWhile_header (n : ℕ) (l : List Bool) : (List.replicate n true ++ false :: l).dropWhile id = false :: l := by sorry
