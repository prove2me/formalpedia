-- Prove2me | Theorems.Thm_GeneralPieces_Sizes_l1_monomial_le
-- name    : GeneralPieces.Sizes.l1_monomial_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:22:41.328433+00:00
-- url     : https://prove2.me/theorems/3c9c49a5-1658-463f-9727-50dc92d2f687
-- title:
--   Sizes: l1 monomial le
-- statement:
--   The Sizes construction uses the l1 monomial le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Sizes.lean#L247-L249
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Sizes.lean#L247-L249

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

theorem GeneralPieces.Sizes.l1_monomial_le (m : ℕ+ →₀ ℕ) (q : ℚ) : l1 (monomial m q) ≤ |q| := by sorry
