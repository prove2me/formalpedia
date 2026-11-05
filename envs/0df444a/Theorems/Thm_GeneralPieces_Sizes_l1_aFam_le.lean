-- Prove2me | Theorems.Thm_GeneralPieces_Sizes_l1_aFam_le
-- name    : GeneralPieces.Sizes.l1_aFam_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:37:13.85066+00:00
-- url     : https://prove2.me/theorems/278c4981-cd94-4170-bfb7-d4fbf71438cc
-- title:
--   Sizes: l1 a Fam le
-- statement:
--   The absolute values of the coefficients of a^μ add up to at most ∏_i 2^{μ_i} = 2^{|μ|}.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Sizes.lean#L278-L291
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Sizes.lean#L278-L291

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

theorem GeneralPieces.Sizes.l1_aFam_le (μ : Ptn) : l1 (aFam μ) ≤ 2 ^ wt μ := by sorry
