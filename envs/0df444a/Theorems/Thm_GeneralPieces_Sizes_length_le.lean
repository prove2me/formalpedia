-- Prove2me | Theorems.Thm_GeneralPieces_Sizes_length_le
-- name    : GeneralPieces.Sizes.length_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:36:48.633343+00:00
-- url     : https://prove2.me/theorems/e2976f83-4386-435e-a933-b8381e2aa779
-- title:
--   Sizes: length le
-- statement:
--   A monomial has at most as many factors as its weight; so a monomial of weight at most h has at
--   most h factors.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Sizes.lean#L153-L155
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Sizes.lean#L153-L155

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

theorem GeneralPieces.Sizes.length_le (a : List ℕ+) : a.length ≤ (toL a).sum := by sorry
