-- Prove2me | Theorems.Thm_GeneralPieces_Series_W_pow
-- name    : GeneralPieces.Series.W_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:17:31.413385+00:00
-- url     : https://prove2.me/theorems/dca03e03-f691-4e7b-ba25-3a4479163a3a
-- title:
--   Series: W pow
-- statement:
--   The Series construction uses the W pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/ReadOff.lean#L29-L31
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/ReadOff.lean#L29-L31

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

theorem GeneralPieces.Series.W_pow (x y : ℤ) (n : ℕ) : W x y ^ n = W (n * x) (n * y) := by sorry
