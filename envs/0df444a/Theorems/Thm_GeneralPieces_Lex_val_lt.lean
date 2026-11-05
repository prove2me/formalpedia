-- Prove2me | Theorems.Thm_GeneralPieces_Lex_val_lt
-- name    : GeneralPieces.Lex.val_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:23:08.997072+00:00
-- url     : https://prove2.me/theorems/6f69d943-27d7-4734-b096-56ba9e8be5e4
-- title:
--   Lex: val lt
-- statement:
--   A string of λ bits, read as an integer, is below 2^λ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Lex.lean#L103-L107
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Lex.lean#L103-L107

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Basic
import Definitions.Def_GeneralPieces_Ring_Bridge
import Mathlib.Combinatorics.Colex
import Mathlib.Data.List.Lex
import Definitions.Def_GeneralPieces_Ring_Lex
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Lex
open AppHalfPieces Finset

theorem GeneralPieces.Lex.val_lt {lam : ℕ} (x : Pieces.Bits lam) : val x < 2 ^ lam := by sorry
