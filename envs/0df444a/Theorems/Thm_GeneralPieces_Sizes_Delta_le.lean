-- Prove2me | Theorems.Thm_GeneralPieces_Sizes_Delta_le
-- name    : GeneralPieces.Sizes.Delta_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:36:26.615063+00:00
-- url     : https://prove2.me/theorems/9dac8680-9545-4c97-b117-b6335e6a18c1
-- title:
--   Sizes: Delta le
-- statement:
--   Δ ≤ (4h+1)·p(4h).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Sizes.lean#L45-L48
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Sizes.lean#L45-L48

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

theorem GeneralPieces.Sizes.Delta_le (h : ℕ) : Delta h ≤ (4 * h + 1) * Partitions.p (4 * h) := by sorry
