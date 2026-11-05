-- Prove2me | Theorems.Thm_GeneralPieces_Dual_zz_eq
-- name    : GeneralPieces.Dual.zz_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:36:25.156261+00:00
-- url     : https://prove2.me/theorems/2e376ab0-86cb-4b2b-8548-d3a96a0d9e60
-- title:
--   Dual: zz eq
-- statement:
--   z_μ equals `ClauseBound.Boson.zz`, the number of that name where the parts are natural numbers.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Dual.lean#L492-L496
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Dual.lean#L492-L496

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

theorem GeneralPieces.Dual.zz_eq (μ : Ptn) : zz μ = ClauseBound.Boson.zz (μ.map fun k : ℕ+ => (k : ℕ)) := by sorry
