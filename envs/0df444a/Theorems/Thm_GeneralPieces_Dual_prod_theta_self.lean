-- Prove2me | Theorems.Thm_GeneralPieces_Dual_prod_theta_self
-- name    : GeneralPieces.Dual.prod_theta_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:35:41.179936+00:00
-- url     : https://prove2.me/theorems/0342ffc7-ac79-406a-bdca-f74dd574e373
-- title:
--   Dual: prod theta self
-- statement:
--   At k_i = μ_i the coefficient is the product of the signs.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Dual.lean#L306-L311
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Dual.lean#L306-L311

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

theorem GeneralPieces.Dual.prod_theta_self (μ : List ℕ+) : (List.zipWith theta μ (μ.map fun n : ℕ+ => (n : ℤ))).prod = sgn μ := by sorry
