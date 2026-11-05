-- Prove2me | Theorems.Thm_GeneralPieces_Sizes_l1_angle_aFam_le
-- name    : GeneralPieces.Sizes.l1_angle_aFam_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:37:19.494653+00:00
-- url     : https://prove2.me/theorems/2cc17e77-bb60-421b-8a14-fb6cabeb6689
-- title:
--   Sizes: l1 angle a Fam le
-- statement:
--   The absolute values of the coefficients of a^⟨i⟩, for a = a^μ and a partition μ of h, add up to
--   at most 2^{2h}·∏_i 2^{μ_i} = 2^{3h}.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Sizes.lean#L325-L328
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Sizes.lean#L325-L328

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

theorem GeneralPieces.Sizes.l1_angle_aFam_le {h : ℕ} (i : ℕ) {μ : Ptn} (hμ : wt μ = h) : l1 (angle h i (aFam μ)) ≤ 2 ^ (3 * h) := by sorry
