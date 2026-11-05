-- Prove2me | Theorems.Thm_GeneralPieces_Lex_lexNum_injOn
-- name    : GeneralPieces.Lex.lexNum_injOn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:22:53.73678+00:00
-- url     : https://prove2.me/theorems/8f197589-27c3-47b2-afe2-b531387a0ca2
-- title:
--   Lex: lex Num inj On
-- statement:
--   Different partitions of h have different numbers.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Lex.lean#L88-L88
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Lex.lean#L88-L88

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

theorem GeneralPieces.Lex.lexNum_injOn (h : ℕ) : Set.InjOn (lexNum h) (ptns h) := by sorry
