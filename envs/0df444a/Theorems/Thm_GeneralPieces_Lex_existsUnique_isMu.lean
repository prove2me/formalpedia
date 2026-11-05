-- Prove2me | Theorems.Thm_GeneralPieces_Lex_existsUnique_isMu
-- name    : GeneralPieces.Lex.existsUnique_isMu
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:23:10.895308+00:00
-- url     : https://prove2.me/theorems/544d10b7-10ef-4e4b-871a-6e2b05eae4e2
-- title:
--   Lex: exists Unique is Mu
-- statement:
--   If 2^λ ≤ p(h), there is exactly one function μ such that μ(x) is the partition of h with number
--   x in the lexicographic list.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Lex.lean#L131-L134
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Lex.lean#L131-L134

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

theorem GeneralPieces.Lex.existsUnique_isMu {lam h : ℕ} (hp : 2 ^ lam ≤ Partitions.p h) : ∃! mu : Pieces.Bits lam → Ptn, IsMu lam h mu := by sorry
