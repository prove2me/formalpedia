-- Prove2me | Theorems.Thm_GeneralPieces_Dual_eq_of_count_le
-- name    : GeneralPieces.Dual.eq_of_count_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:36:04.0004+00:00
-- url     : https://prove2.me/theorems/4559c560-628c-43b4-a4a7-92190ea12942
-- title:
--   Dual: eq of count le
-- statement:
--   «… otherwise μ = ν, because |μ| = |ν|».
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Dual.lean#L412-L419
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Dual.lean#L412-L419

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

theorem GeneralPieces.Dual.eq_of_count_le (μ ν : Ptn) (hc : ∀ k, μ.count k ≤ ν.count k) (hw : wt μ = wt ν) : μ = ν := by sorry
