-- Prove2me | Theorems.Thm_GeneralPieces_Sizes_sum_toL_toList
-- name    : GeneralPieces.Sizes.sum_toL_toList
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:37:45.2852+00:00
-- url     : https://prove2.me/theorems/89508014-b0cc-474b-ae42-6cbcb30e2559
-- title:
--   Sizes: sum to L to List
-- statement:
--   The Sizes construction uses the sum to L to List property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Sizes.lean#L355-L360
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Sizes.lean#L355-L360

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

theorem GeneralPieces.Sizes.sum_toL_toList (m : ℕ+ →₀ ℕ) : (toL (Finsupp.toMultiset m).toList).sum = Finsupp.weight wgt m := by sorry
