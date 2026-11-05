-- Prove2me | Theorems.Thm_GeneralPieces_Sizes_wt_erase_le
-- name    : GeneralPieces.Sizes.wt_erase_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:36:40.423775+00:00
-- url     : https://prove2.me/theorems/a7f2b6bd-da1e-4ed5-891f-114a7337b747
-- title:
--   Sizes: wt erase le
-- statement:
--   The Sizes construction uses the wt erase le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Sizes.lean#L103-L107
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Sizes.lean#L103-L107

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

theorem GeneralPieces.Sizes.wt_erase_le (σ : Ptn) (l : ℕ+) : wt (σ.erase l) ≤ wt σ := by sorry
