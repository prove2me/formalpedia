-- Prove2me | Theorems.Thm_GeneralPieces_Sizes_mul_count_le_wt
-- name    : GeneralPieces.Sizes.mul_count_le_wt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:36:43.400849+00:00
-- url     : https://prove2.me/theorems/731b4621-dcaf-4721-9ff6-4d95e7cf921e
-- title:
--   Sizes: mul count le wt
-- statement:
--   k·m_k(σ) ≤ |σ|.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Sizes.lean#L110-L121
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Sizes.lean#L110-L121

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

theorem GeneralPieces.Sizes.mul_count_le_wt (σ : Ptn) (k : ℕ+) : (k : ℕ) * σ.count k ≤ wt σ := by sorry
