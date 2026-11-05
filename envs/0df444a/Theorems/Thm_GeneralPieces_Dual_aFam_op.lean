-- Prove2me | Theorems.Thm_GeneralPieces_Dual_aFam_op
-- name    : GeneralPieces.Dual.aFam_op
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:35:48.817284+00:00
-- url     : https://prove2.me/theorems/8ededfff-7907-4067-9542-c0ddace2f720
-- title:
--   Dual: a Fam op
-- statement:
--   «Therefore a^μ[−h]·b = ∏_i ∇_{μ_i} b.»
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Dual.lean#L346-L350
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Dual.lean#L346-L350

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

theorem GeneralPieces.Dual.aFam_op (h : ℕ) (μ : List ℕ+) (hμ : wt (μ : Multiset ℕ+) = h) (b : V) (hb : b ∈ VE h) :
    op (aFam (μ : Multiset ℕ+)) (-(h : ℤ)) b = nablas (μ.map fun n : ℕ+ => (n : ℤ)) b := by sorry
