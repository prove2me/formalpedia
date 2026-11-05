-- Prove2me | Theorems.Thm_GeneralPieces_Lex_rank_injOn
-- name    : GeneralPieces.Lex.rank_injOn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:36:19.44023+00:00
-- url     : https://prove2.me/theorems/1729adad-690c-49e1-a5f1-931aa940bea2
-- title:
--   Lex: rank inj On
-- statement:
--   Different elements of the list have different numbers.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Lex.lean#L59-L64
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Lex.lean#L59-L64

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

theorem GeneralPieces.Lex.rank_injOn (hf : Set.InjOn f S) : Set.InjOn (fun a => #{c ∈ S | f c < f a}) S := by sorry
