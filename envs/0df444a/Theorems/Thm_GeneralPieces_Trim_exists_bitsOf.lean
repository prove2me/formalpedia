-- Prove2me | Theorems.Thm_GeneralPieces_Trim_exists_bitsOf
-- name    : GeneralPieces.Trim.exists_bitsOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:47:05.087614+00:00
-- url     : https://prove2.me/theorems/6982d9ee-9ab7-4c5e-89a2-27be1a361bd3
-- title:
--   Trim: exists bits Of
-- statement:
--   Every word of n bits is the word of a function.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Trim/Prog.lean#L35-L37
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Trim/Prog.lean#L35-L37

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_DefGenPieces_Progs
import Definitions.Def_GeneralPieces_Trim_Prog
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open GeneralPieces
open Finset Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.Gen
open GeneralPieces.Trim

theorem GeneralPieces.Trim.exists_bitsOf {n : ℕ} {w : List Bool} (hw : w.length = n) : ∃ x : Pieces.Bits n, bitsOf x = w := by sorry
