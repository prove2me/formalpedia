-- Prove2me | Theorems.Thm_GeneralPieces_Sizes_card_le_wt
-- name    : GeneralPieces.Sizes.card_le_wt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:26:17.269571+00:00
-- url     : https://prove2.me/theorems/6ece120f-1906-4a34-898a-bbe179b4ff9d
-- title:
--   Sizes: card le wt
-- statement:
--   A partition has at most as many parts as its weight.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Sizes.lean#L84-L91
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Sizes.lean#L84-L91

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_GeneralPieces_Ring_Lex
import Definitions.Def_ClauseBound_Boson_Size
import Definitions.Def_GeneralPieces_Ring_Sizes
import Theorems.Thm_GeneralPieces_Lex_IsMu_wt

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Sizes
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring

theorem GeneralPieces.Sizes.card_le_wt (σ : Ptn) : Multiset.card σ ≤ wt σ := by sorry
