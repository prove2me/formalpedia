-- Prove2me | Theorems.Thm_GeneralPieces_Dual_nablas_tpow_self
-- name    : GeneralPieces.Dual.nablas_tpow_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:36:04.104207+00:00
-- url     : https://prove2.me/theorems/6ad299b0-e470-434e-96ed-1f54c9b3e13e
-- title:
--   Dual: nablas tpow self
-- statement:
--   «… and it is z_μ.»
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Dual.lean#L441-L448
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Dual.lean#L441-L448

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

theorem GeneralPieces.Dual.nablas_tpow_self (μ : List ℕ+) : nablas (μ.map fun n : ℕ+ => (n : ℤ)) (tpow (μ : Multiset ℕ+)) = C (zz (μ : Multiset ℕ+) : ℚ) := by sorry
