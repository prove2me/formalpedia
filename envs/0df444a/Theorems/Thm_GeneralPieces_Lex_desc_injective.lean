-- Prove2me | Theorems.Thm_GeneralPieces_Lex_desc_injective
-- name    : GeneralPieces.Lex.desc_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:36:26.813818+00:00
-- url     : https://prove2.me/theorems/8c313b1e-736b-4475-8280-8e16c9c65dde
-- title:
--   Lex: desc injective
-- statement:
--   A partition is determined by its nonincreasing sequence.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Lex.lean#L81-L85
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Lex.lean#L81-L85

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

theorem GeneralPieces.Lex.desc_injective : Function.Injective desc := by sorry
