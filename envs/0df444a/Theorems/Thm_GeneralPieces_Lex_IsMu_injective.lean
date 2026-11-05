-- Prove2me | Theorems.Thm_GeneralPieces_Lex_IsMu_injective
-- name    : GeneralPieces.Lex.IsMu.injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:23:04.403161+00:00
-- url     : https://prove2.me/theorems/9df1572e-5af9-496b-96b0-d42a74edc8e7
-- title:
--   Is Mu: injective
-- statement:
--   μ is injective.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Lex.lean#L122-L123
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Lex.lean#L122-L123

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

theorem GeneralPieces.Lex.IsMu.injective {lam h : ℕ} {mu : Pieces.Bits lam → Ptn} (hmu : IsMu lam h mu) : Function.Injective mu := by sorry
