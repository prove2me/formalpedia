-- Prove2me | Theorems.Thm_GeneralPieces_Sizes_bet_eq
-- name    : GeneralPieces.Sizes.bet_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:36:29.255239+00:00
-- url     : https://prove2.me/theorems/a4bf473d-6f20-45ed-97b3-05793d2311e5
-- title:
--   Sizes: bet eq
-- statement:
--   The coefficient `ClauseBound.Boson.bet n r` of the matrices `ClauseBound.Boson.op` is C(r−1,
--   n−1) for r ≠ 0.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Sizes.lean#L54-L56
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Sizes.lean#L54-L56

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

theorem GeneralPieces.Sizes.bet_eq (n : ℕ+) {r : ℤ} (hr : r ≠ 0) : ClauseBound.Boson.bet n r = binom (r - 1) ((n : ℤ) - 1) := by sorry
