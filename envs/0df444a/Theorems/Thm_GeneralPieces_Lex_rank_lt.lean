-- Prove2me | Theorems.Thm_GeneralPieces_Lex_rank_lt
-- name    : GeneralPieces.Lex.rank_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:22:36.21328+00:00
-- url     : https://prove2.me/theorems/bca075dd-1f8f-469d-a855-2d3f3cdb2a9f
-- title:
--   Lex: rank lt
-- statement:
--   If f(a) < f(b) and a is in the list, fewer elements come before a than before b.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Lex.lean#L49-L52
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Lex.lean#L49-L52

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

theorem GeneralPieces.Lex.rank_lt {a b : α} (ha : a ∈ S) (hab : f a < f b) : #{c ∈ S | f c < f a} < #{c ∈ S | f c < f b} := by sorry
