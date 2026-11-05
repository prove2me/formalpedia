-- Prove2me | Theorems.Thm_GeneralPieces_Series_dW_pow
-- name    : GeneralPieces.Series.dW_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:06:55.126118+00:00
-- url     : https://prove2.me/theorems/983f1b41-142b-4ee6-8ff8-4825351eb82b
-- title:
--   Series: d W pow
-- statement:
--   (ω₁ − ω₂)^H = Σ_i (−1)^i·C(H,i)·ω₁^{H−i}·ω₂^i.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/ReadOff.lean#L34-L40
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/ReadOff.lean#L34-L40

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

theorem GeneralPieces.Series.dW_pow (H : ℕ) : dW ^ H = ∑ i ∈ range (H + 1), ((-1) ^ i * (H.choose i : ℚ)) • W (H - i) i := by sorry
