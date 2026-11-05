-- Prove2me | Theorems.Thm_GeneralPieces_Series_cfP_dW_pow_mul
-- name    : GeneralPieces.Series.cfP_dW_pow_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:06:43.250001+00:00
-- url     : https://prove2.me/theorems/866a3a49-a651-49e8-8acd-50f514608528
-- title:
--   Series: cf P d W pow mul
-- statement:
--   The coefficients of (ω₁ − ω₂)^H·f in 𝓛₊.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/ReadOff.lean#L43-L47
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/ReadOff.lean#L43-L47

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

theorem GeneralPieces.Series.cfP_dW_pow_mul (H : ℕ) (f : Lp) (x y : ℤ) :
    cfP (toP dW ^ H * f) x y = ∑ i ∈ range (H + 1), ((-1) ^ i * (H.choose i : ℚ)) * cfP f (x - (H - i)) (y - i) := by sorry
