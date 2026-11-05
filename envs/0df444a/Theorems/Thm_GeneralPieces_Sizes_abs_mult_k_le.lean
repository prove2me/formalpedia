-- Prove2me | Theorems.Thm_GeneralPieces_Sizes_abs_mult_k_le
-- name    : GeneralPieces.Sizes.abs_mult_k_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:36:49.155006+00:00
-- url     : https://prove2.me/theorems/6584d90d-243c-464f-8df5-e8db39451ef5
-- title:
--   Sizes: abs mult k le
-- statement:
--   The multipliers of the second sum are at most 4h·2^{5h} in absolute value.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Sizes.lean#L139-L147
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Sizes.lean#L139-L147

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

theorem GeneralPieces.Sizes.abs_mult_k_le {h : ℕ} {n k : ℕ+} (hn : (n : ℕ) ≤ h) {σ : Ptn} (h2 : wt σ ≤ 4 * h) (hk : k ∈ σ) :
    |binom (-((k : ℕ) : ℤ) - 1) ((n : ℤ) - 1) * ((k : ℕ) * σ.count k)| ≤ 4 * h * 2 ^ (5 * h) := by sorry
