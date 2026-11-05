-- Prove2me | Theorems.Thm_GeneralPieces_Lex_hOf_eq
-- name    : GeneralPieces.Lex.hOf_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:30:07.632204+00:00
-- url     : https://prove2.me/theorems/61c3b757-82dc-4503-a3dd-b5660f044028
-- title:
--   Lex: h Of eq
-- statement:
--   The h of the appendix equals the h defined by `ClauseBound.Part.hOf`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Lex.lean#L36-L40
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Lex.lean#L36-L40

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

theorem GeneralPieces.Lex.hOf_eq (lam : ℕ) : AppHalfPieces.hOf lam = ClauseBound.Part.hOf lam := by sorry
