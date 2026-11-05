-- Prove2me | Theorems.Thm_GeneralPieces_Sizes_l1_angle_le
-- name    : GeneralPieces.Sizes.l1_angle_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:37:21.780251+00:00
-- url     : https://prove2.me/theorems/bd1d248b-82e7-4c59-a972-59ea3e89eed2
-- title:
--   Sizes: l1 angle le
-- statement:
--   The absolute values of the coefficients of a^⟨i⟩ add up to at most 2^{2h} times the sum for a.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Sizes.lean#L305-L321
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Sizes.lean#L305-L321

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

theorem GeneralPieces.Sizes.l1_angle_le (h i : ℕ) (a : V) : l1 (angle h i a) ≤ 2 ^ (2 * h) * l1 a := by sorry
