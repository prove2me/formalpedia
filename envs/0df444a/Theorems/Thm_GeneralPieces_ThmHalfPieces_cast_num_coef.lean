-- Prove2me | Theorems.Thm_GeneralPieces_ThmHalfPieces_cast_num_coef
-- name    : GeneralPieces.ThmHalfPieces.cast_num_coef
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:25:06.030207+00:00
-- url     : https://prove2.me/theorems/8d9c565f-2b1f-4ebe-b0f5-154989534d18
-- title:
--   Thm Half Pieces: cast num coef
-- statement:
--   A coefficient of an integer polynomial, as an integer.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/ThmHalfPieces.lean#L43-L46
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/ThmHalfPieces.lean#L43-L46

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Bits
import Definitions.Def_ClauseBound_Boson_Final
import Definitions.Def_GeneralPieces_Ring_ThmHalfPieces
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.ThmHalfPieces
open AppHalfPieces Finset GeneralPieces.Ring GeneralPieces.Sizes GeneralPieces.Lex

theorem GeneralPieces.ThmHalfPieces.cast_num_coef {f : V} (hf : IsInt f) (μ : Ptn) : (((coef μ f).num : ℤ) : ℚ) = coef μ f := by sorry
