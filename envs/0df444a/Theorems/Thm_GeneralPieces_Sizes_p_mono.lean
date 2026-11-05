-- Prove2me | Theorems.Thm_GeneralPieces_Sizes_p_mono
-- name    : GeneralPieces.Sizes.p_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:25:10.899904+00:00
-- url     : https://prove2.me/theorems/502ee22f-9c65-41b0-9e51-c95f867f0154
-- title:
--   Sizes: p mono
-- statement:
--   p is nondecreasing.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Sizes.lean#L42-L42
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Sizes.lean#L42-L42

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_GeneralPieces_Ring_Lex
import Definitions.Def_ClauseBound_Boson_Size
import Definitions.Def_GeneralPieces_Ring_Sizes
import Theorems.Thm_ClauseBound_Part_p_mono

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Sizes
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring

theorem GeneralPieces.Sizes.p_mono {E E' : ℕ} (hE : E ≤ E') : Partitions.p E ≤ Partitions.p E' := by sorry
