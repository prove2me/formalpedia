-- Prove2me | Theorems.Thm_GeneralPieces_Dual_display
-- name    : GeneralPieces.Dual.display
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:35:14.78758+00:00
-- url     : https://prove2.me/theorems/754a323a-a3d7-490c-982b-a3ad6d32efbe
-- title:
--   Dual: display
-- statement:
--   The display in the proof: for b ∈ V_h, (∏_i y_{μ_i})[−h]·b = Σ over the tuples (k_i) with Σ k_i =
--   h and k_i ≥ 1 of ∏_i ϑ_{μ_i}(k_i)·∏_i ∇_{k_i} b.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Dual.lean#L230-L246
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Dual.lean#L230-L246

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_ClauseBound_Boson_Dual
import Definitions.Def_GeneralPieces_Ring_Dual
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Dual
open Finset MvPolynomial AppHalfPieces

theorem GeneralPieces.Dual.display (h : ℕ) (μ : List ℕ+) (b : V) (hb : b ∈ VE h) :
    op (μ.map y).prod (-(h : ℤ)) b = ∑ ks ∈ posTuples μ.length h, (((List.zipWith theta μ ks).prod : ℤ) : ℚ) • nablas ks b := by sorry
