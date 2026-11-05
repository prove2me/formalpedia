-- Prove2me | Theorems.Thm_GeneralPieces_Sizes_l1_y_le
-- name    : GeneralPieces.Sizes.l1_y_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:37:13.945196+00:00
-- url     : https://prove2.me/theorems/82bb7752-2edc-4864-8f32-416ce19ca706
-- title:
--   Sizes: l1 y le
-- statement:
--   The coefficients of y_n add up to at most 2^n.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Sizes.lean#L262-L271
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Sizes.lean#L262-L271

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

theorem GeneralPieces.Sizes.l1_y_le (n : ℕ+) : l1 (y n) ≤ 2 ^ (n : ℕ) := by sorry
