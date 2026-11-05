-- Prove2me | Theorems.Thm_GeneralPieces_Lex_val_eq
-- name    : GeneralPieces.Lex.val_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:36:31.057756+00:00
-- url     : https://prove2.me/theorems/47eba8aa-0bfc-4612-bcd1-0fa3f6b26ae8
-- title:
--   Lex: val eq
-- statement:
--   A string read as an integer is the sum of the 2^i over the positions i of its ones.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Lex.lean#L97-L100
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Lex.lean#L97-L100

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

theorem GeneralPieces.Lex.val_eq {lam : ℕ} (x : Pieces.Bits lam) : val x = ∑ i ∈ (univ.filter fun i : Fin lam => x i = true).map Fin.valEmbedding, 2 ^ i := by sorry
