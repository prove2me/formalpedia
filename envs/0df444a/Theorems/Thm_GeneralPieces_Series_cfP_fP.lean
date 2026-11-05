-- Prove2me | Theorems.Thm_GeneralPieces_Series_cfP_fP
-- name    : GeneralPieces.Series.cfP_fP
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:40:32.00934+00:00
-- url     : https://prove2.me/theorems/254e04e2-0e46-4e6f-bc8e-28341121fa90
-- title:
--   Series: cf P f P
-- statement:
--   The coefficients of f₊. The start of the series cuts nothing off: there are no terms for r > E.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Expansion.lean#L45-L53
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Expansion.lean#L45-L53

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

theorem GeneralPieces.Series.cfP_fP (a b : List ℕ) (π σ : Multiset ℕ) (x y : ℤ) :
    cfP (fP a b π σ) x y = if x + y = -((a.sum : ℤ) + b.sum) then (mul2 a (x + a.sum) b (y + b.sum) π σ : ℚ) else 0 := by sorry
