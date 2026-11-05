-- Prove2me | Theorems.Thm_GeneralPieces_Sizes_l1_add_le
-- name    : GeneralPieces.Sizes.l1_add_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:37:13.327194+00:00
-- url     : https://prove2.me/theorems/d2ade6f1-305f-4676-af71-0298ce0164aa
-- title:
--   Sizes: l1 add le
-- statement:
--   The Sizes construction uses the l1 add le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Sizes.lean#L229-L233
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Sizes.lean#L229-L233

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_GeneralPieces_Ring_Lex
import Definitions.Def_ClauseBound_Boson_Size
import Definitions.Def_GeneralPieces_Ring_Sizes
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Sizes
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring

theorem GeneralPieces.Sizes.l1_add_le (a b : V) : l1 (a + b) ≤ l1 a + l1 b := by sorry
