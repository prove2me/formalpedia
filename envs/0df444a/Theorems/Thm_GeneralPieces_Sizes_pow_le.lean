-- Prove2me | Theorems.Thm_GeneralPieces_Sizes_pow_le
-- name    : GeneralPieces.Sizes.pow_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:36:55.534201+00:00
-- url     : https://prove2.me/theorems/a5afe6ef-c6a9-48af-8c49-a006d79c8e8f
-- title:
--   Sizes: pow le
-- statement:
--   (32h²·2^{5h})^h ≤ 2^{12h²}, for h ≥ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Sizes.lean#L194-L203
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Sizes.lean#L194-L203

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

theorem GeneralPieces.Sizes.pow_le {h : ℕ} (hh : 1 ≤ h) : (32 * h ^ 2 * 2 ^ (5 * h)) ^ h ≤ 2 ^ (12 * h ^ 2) := by sorry
