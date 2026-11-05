-- Prove2me | Theorems.Thm_GeneralPieces_Sizes_toFinset_toN
-- name    : GeneralPieces.Sizes.toFinset_toN
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:36:32.578297+00:00
-- url     : https://prove2.me/theorems/3d861077-1660-4d0d-bab1-7266a68fe3ec
-- title:
--   Sizes: to Finset to N
-- statement:
--   The Sizes construction uses the to Finset to N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Sizes.lean#L58-L58
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Sizes.lean#L58-L58

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

theorem GeneralPieces.Sizes.toFinset_toN (π : Ptn) : (toN π).toFinset = π.toFinset.image fun k : ℕ+ => (k : ℕ) := by sorry
