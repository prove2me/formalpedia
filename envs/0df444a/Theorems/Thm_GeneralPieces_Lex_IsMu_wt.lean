-- Prove2me | Theorems.Thm_GeneralPieces_Lex_IsMu_wt
-- name    : GeneralPieces.Lex.IsMu.wt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:29:09.867444+00:00
-- url     : https://prove2.me/theorems/6494424b-fc13-4a05-99c4-2acd03ce7609
-- title:
--   Is Mu: wt
-- statement:
--   μ(x) is a partition of h.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Lex.lean#L126-L127
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Lex.lean#L126-L127

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

theorem GeneralPieces.Lex.IsMu.wt {lam h : ℕ} {mu : Pieces.Bits lam → Ptn} (hmu : IsMu lam h mu) (x : Pieces.Bits lam) : AppHalfPieces.wt (mu x) = h := by sorry
