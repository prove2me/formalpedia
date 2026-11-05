-- Prove2me | Theorems.Thm_GeneralPieces_Series_sum_range_two_mul
-- name    : GeneralPieces.Series.sum_range_two_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:18:33.192698+00:00
-- url     : https://prove2.me/theorems/62d6aa55-d732-4424-8fdc-b7b794451e75
-- title:
--   Series: sum range two mul
-- statement:
--   For a monomial of weight h' ≤ h the sum over i ≤ 2h stops at H = h' + h, because C(H,i) = 0 for
--   i > H.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/LemmaQ.lean#L46-L50
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/LemmaQ.lean#L46-L50

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Series_Constant
import Definitions.Def_ClauseBound_Boson_Defs2
import Definitions.Def_GeneralPieces_Series_LemmaQ
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Series
open ClauseBound.Boson Finset

theorem GeneralPieces.Series.sum_range_two_mul {H h : ℕ} (hH : H ≤ 2 * h) (g : ℕ → ℤ) :
    ∑ i ∈ range (2 * h + 1), (-1) ^ i * (H.choose i : ℤ) * g i = ∑ i ∈ range (H + 1), (-1) ^ i * (H.choose i : ℤ) * g i := by sorry
