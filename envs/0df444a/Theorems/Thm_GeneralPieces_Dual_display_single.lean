-- Prove2me | Theorems.Thm_GeneralPieces_Dual_display_single
-- name    : GeneralPieces.Dual.display_single
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:35:46.249817+00:00
-- url     : https://prove2.me/theorems/753647c9-9dc9-427f-ab43-1974d9578c80
-- title:
--   Dual: display single
-- statement:
--   The display has one term: (∏_i y_{μ_i})[−h]·b = ∏_i (−1)^{μ_i−1}·∏_i ∇_{μ_i} b, for a partition
--   μ of h and b ∈ V_h.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Dual.lean#L315-L331
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Dual.lean#L315-L331

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

theorem GeneralPieces.Dual.display_single (h : ℕ) (μ : List ℕ+) (hμ : wt (μ : Multiset ℕ+) = h) (b : V) (hb : b ∈ VE h) :
    op (μ.map y).prod (-(h : ℤ)) b = (sgn μ : ℚ) • nablas (μ.map fun n : ℕ+ => (n : ℤ)) b := by sorry
