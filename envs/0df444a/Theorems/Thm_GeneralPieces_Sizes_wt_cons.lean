-- Prove2me | Theorems.Thm_GeneralPieces_Sizes_wt_cons
-- name    : GeneralPieces.Sizes.wt_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:37:23.730227+00:00
-- url     : https://prove2.me/theorems/7ccb8d4e-cd8c-4f2a-987e-f0cac3c34e88
-- title:
--   Sizes: wt cons
-- statement:
--   The Sizes construction uses the wt cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Sizes.lean#L273-L275
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Sizes.lean#L273-L275

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_GeneralPieces_Ring_Lex
import Definitions.Def_ClauseBound_Boson_Size
import Definitions.Def_GeneralPieces_Ring_Sizes
import Theorems.Thm_ClauseBound_Boson_Text_wt_cons
import Theorems.Thm_GeneralPieces_Lex_IsMu_wt

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Sizes
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring

theorem GeneralPieces.Sizes.wt_cons (n : ℕ+) (μ : Ptn) : wt (n ::ₘ μ) = n + wt μ := by sorry
