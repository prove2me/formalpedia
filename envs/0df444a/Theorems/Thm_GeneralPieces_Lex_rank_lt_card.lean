-- Prove2me | Theorems.Thm_GeneralPieces_Lex_rank_lt_card
-- name    : GeneralPieces.Lex.rank_lt_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:22:43.943982+00:00
-- url     : https://prove2.me/theorems/5cb1acd2-4973-4d6c-b2f7-5b4a98c93787
-- title:
--   Lex: rank lt card
-- statement:
--   The number of an element of the list is below the length of the list.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Lex.lean#L55-L56
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Lex.lean#L55-L56

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
variable {α β : Type} [LinearOrder β] [DecidableRel fun a b : β => a < b] (S : Finset α) (f : α → β)

theorem GeneralPieces.Lex.rank_lt_card {a : α} (ha : a ∈ S) : #{c ∈ S | f c < f a} < #S := by sorry
