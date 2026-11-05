-- Prove2me | Theorems.Thm_GeneralPieces_Series_cfM_dW_pow_mul
-- name    : GeneralPieces.Series.cfM_dW_pow_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:17:37.799509+00:00
-- url     : https://prove2.me/theorems/fadc270c-44a8-41b3-986b-f7469a6889ec
-- title:
--   Series: cf M d W pow mul
-- statement:
--   The coefficients of (ω₁ − ω₂)^H·f in 𝓛₋.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/ReadOff.lean#L50-L54
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/ReadOff.lean#L50-L54

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

theorem GeneralPieces.Series.cfM_dW_pow_mul (H : ℕ) (f : Lm) (x y : ℤ) :
    cfM (toM dW ^ H * f) x y = ∑ i ∈ range (H + 1), ((-1) ^ i * (H.choose i : ℚ)) * cfM f (x - (H - i)) (y - i) := by sorry
