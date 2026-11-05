-- Prove2me | Theorems.Thm_GeneralPieces_Dual_nablas_snoc_tpow
-- name    : GeneralPieces.Dual.nablas_snoc_tpow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:25:00.81393+00:00
-- url     : https://prove2.me/theorems/834d3d08-14fe-45e8-bea2-64dbf58a2e17
-- title:
--   Dual: nablas snoc tpow
-- statement:
--   The differentiation that is listed last is applied first.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Dual.lean#L383-L386
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Dual.lean#L383-L386

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

theorem GeneralPieces.Dual.nablas_snoc_tpow (μ : List ℕ+) (n : ℕ+) (ν : Ptn) : nablas ((μ ++ [n]).map fun n : ℕ+ => (n : ℤ)) (tpow ν) =
    (((n : ℕ) : ℚ) * (ν.count n : ℚ)) • nablas (μ.map fun n : ℕ+ => (n : ℤ)) (tpow (ν.erase n)) := by sorry
