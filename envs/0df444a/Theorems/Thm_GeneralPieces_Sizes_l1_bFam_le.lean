-- Prove2me | Theorems.Thm_GeneralPieces_Sizes_l1_bFam_le
-- name    : GeneralPieces.Sizes.l1_bFam_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:37:29.312995+00:00
-- url     : https://prove2.me/theorems/824f6d71-0397-45b4-a292-8fee854cdb2a
-- title:
--   Sizes: l1 b Fam le
-- statement:
--   b^μ has one coefficient, h!/z_μ with h = |μ|; it is at most h!.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Sizes.lean#L334-L343
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Sizes.lean#L334-L343

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_GeneralPieces_Ring_Lex
import Definitions.Def_ClauseBound_Boson_Size
import Definitions.Def_GeneralPieces_Ring_Sizes
import Theorems.Thm_GeneralPieces_Lex_IsMu_wt

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Sizes
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring

theorem GeneralPieces.Sizes.l1_bFam_le (μ : Ptn) : l1 (bFam μ) ≤ (wt μ).factorial := by sorry
