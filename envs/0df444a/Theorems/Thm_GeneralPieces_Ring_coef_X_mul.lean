-- Prove2me | Theorems.Thm_GeneralPieces_Ring_coef_X_mul
-- name    : GeneralPieces.Ring.coef_X_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:01:29.324321+00:00
-- url     : https://prove2.me/theorems/fc06ecb2-bf05-4d5a-9017-c24da915a885
-- title:
--   Ring: coef X mul
-- statement:
--   The coefficients of t_l·f.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Bridge.lean#L74-L77
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Bridge.lean#L74-L77

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Defs
import Definitions.Def_ClauseBound_Boson_Text
import Mathlib.RingTheory.Derivation.Lie
import Definitions.Def_GeneralPieces_Ring_Bridge
import Theorems.Thm_ClauseBound_Boson_Text_coef_X_mul

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Ring
open AppHalfPieces MvPolynomial Finset

theorem GeneralPieces.Ring.coef_X_mul (π : Ptn) (l : ℕ+) (f : V) : coef π (X l * f) = if l ∈ π then coef (π.erase l) f else 0 := by sorry
