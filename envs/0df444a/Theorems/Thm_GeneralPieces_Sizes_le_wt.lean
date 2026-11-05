-- Prove2me | Theorems.Thm_GeneralPieces_Sizes_le_wt
-- name    : GeneralPieces.Sizes.le_wt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:26:15.96436+00:00
-- url     : https://prove2.me/theorems/c61d7820-5ca0-4e0d-af25-028a4cd031dd
-- title:
--   Sizes: le wt
-- statement:
--   The Sizes construction uses the le wt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Sizes.lean#L99-L101
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Sizes.lean#L99-L101

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

theorem GeneralPieces.Sizes.le_wt {σ : Ptn} {l : ℕ+} (hl : l ∈ σ) : (l : ℕ) ≤ wt σ := by sorry
