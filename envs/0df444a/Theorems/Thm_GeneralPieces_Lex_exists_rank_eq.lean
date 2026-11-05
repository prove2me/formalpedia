-- Prove2me | Theorems.Thm_GeneralPieces_Lex_exists_rank_eq
-- name    : GeneralPieces.Lex.exists_rank_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:22:52.750108+00:00
-- url     : https://prove2.me/theorems/c72a28e1-fe49-401f-a040-3942908140b5
-- title:
--   Lex: exists rank eq
-- statement:
--   Every number below the length of the list is the number of an element.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Lex.lean#L67-L74
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Lex.lean#L67-L74

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

theorem GeneralPieces.Lex.exists_rank_eq (hf : Set.InjOn f S) {j : ℕ} (hj : j < #S) : ∃ a ∈ S, #{c ∈ S | f c < f a} = j := by sorry
