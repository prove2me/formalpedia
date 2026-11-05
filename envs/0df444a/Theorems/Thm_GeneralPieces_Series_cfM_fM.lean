-- Prove2me | Theorems.Thm_GeneralPieces_Series_cfM_fM
-- name    : GeneralPieces.Series.cfM_fM
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:04:13.56537+00:00
-- url     : https://prove2.me/theorems/0f308150-5dab-4e4a-b541-16aeb4712864
-- title:
--   Series: cf M f M
-- statement:
--   The coefficients of f₋. The start of the series cuts nothing off: there are no terms for r < −E.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Expansion.lean#L56-L64
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Expansion.lean#L56-L64

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Series_Rings
import Definitions.Def_ClauseBound_Boson_Defs
import Definitions.Def_GeneralPieces_Series_Expansion
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Series
open ClauseBound.Boson

theorem GeneralPieces.Series.cfM_fM (a b : List ℕ) (π σ : Multiset ℕ) (x y : ℤ) :
    cfM (fM a b π σ) x y = if x + y = -((a.sum : ℤ) + b.sum) then (mul2 b (y + b.sum) a (x + a.sum) π σ : ℚ) else 0 := by sorry
