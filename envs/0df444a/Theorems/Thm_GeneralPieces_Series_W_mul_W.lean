-- Prove2me | Theorems.Thm_GeneralPieces_Series_W_mul_W
-- name    : GeneralPieces.Series.W_mul_W
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:17:30.909208+00:00
-- url     : https://prove2.me/theorems/94bd6081-be53-4d95-8793-f43d9edd0e42
-- title:
--   Series: W mul W
-- statement:
--   The Series construction uses the W mul W property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/ReadOff.lean#L26-L27
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/ReadOff.lean#L26-L27

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Series_OneLaurent
import Mathlib.Data.Nat.Choose.Sum
import Definitions.Def_GeneralPieces_Series_ReadOff
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Series
open ClauseBound.Boson Finset

theorem GeneralPieces.Series.W_mul_W (x y x' y' : ℤ) : W x y * W x' y' = W (x + x') (y + y') := by sorry
