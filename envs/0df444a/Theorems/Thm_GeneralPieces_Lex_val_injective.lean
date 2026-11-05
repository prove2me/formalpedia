-- Prove2me | Theorems.Thm_GeneralPieces_Lex_val_injective
-- name    : GeneralPieces.Lex.val_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:23:05.036517+00:00
-- url     : https://prove2.me/theorems/a75273f0-d436-4c8a-9bb5-e440a4496304
-- title:
--   Lex: val injective
-- statement:
--   Different strings are different integers.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Lex.lean#L110-L117
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Lex.lean#L110-L117

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

theorem GeneralPieces.Lex.val_injective (lam : ℕ) : Function.Injective (val (lam := lam)) := by sorry
