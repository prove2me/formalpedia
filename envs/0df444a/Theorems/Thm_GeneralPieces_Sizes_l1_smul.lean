-- Prove2me | Theorems.Thm_GeneralPieces_Sizes_l1_smul
-- name    : GeneralPieces.Sizes.l1_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:23:09.575434+00:00
-- url     : https://prove2.me/theorems/5e6f6454-2f80-424a-927c-966062880818
-- title:
--   Sizes: l1 smul
-- statement:
--   The Sizes construction uses the l1 smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Sizes.lean#L243-L245
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Sizes.lean#L243-L245

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

theorem GeneralPieces.Sizes.l1_smul (q : ℚ) (a : V) : l1 (q • a) = |q| * l1 a := by sorry
