-- Prove2me | Theorems.Thm_GeneralPieces_Sizes_abs_factor_b_le
-- name    : GeneralPieces.Sizes.abs_factor_b_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:23:16.83845+00:00
-- url     : https://prove2.me/theorems/a950ffc7-02e8-4b35-8bf3-df2c0d1e208a
-- title:
--   Sizes: abs factor b le
-- statement:
--   The factors with b in (54) and (55) are at most h!·2^{12h²} in absolute value.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Sizes.lean#L380-L388
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Sizes.lean#L380-L388

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_GeneralPieces_Ring_Lex
import Definitions.Def_ClauseBound_Boson_Size
import Definitions.Def_GeneralPieces_Ring_Sizes
import Theorems.Thm_GeneralPieces_Lex_IsMu_wt

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Sizes
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring

theorem GeneralPieces.Sizes.abs_factor_b_le {h : ℕ} (hh : 1 ≤ h) {ν : Ptn} (hν : wt ν = h) (r : ℤ) {σ' σ : Ptn} (h1 : wt σ' ≤ 4 * h) (h2 : wt σ ≤ 4 * h) :
    |coef σ' (op (bFam ν) r (tpow σ))| ≤ h.factorial * 2 ^ (12 * h ^ 2) := by sorry
