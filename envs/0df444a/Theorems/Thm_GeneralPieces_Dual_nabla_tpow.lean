-- Prove2me | Theorems.Thm_GeneralPieces_Dual_nabla_tpow
-- name    : GeneralPieces.Dual.nabla_tpow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:35:52.585329+00:00
-- url     : https://prove2.me/theorems/3aac0f25-a117-4847-b27e-7148e07fc4b8
-- title:
--   Dual: nabla tpow
-- statement:
--   ∇_n t^ν = n·m_n(ν)·t^{ν−n}, where ν − n is ν without one part n.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Dual.lean#L357-L367
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Dual.lean#L357-L367

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

theorem GeneralPieces.Dual.nabla_tpow (n : ℕ+) (ν : Ptn) : nabla (n : ℤ) (tpow ν) = (((n : ℕ) : ℚ) * (ν.count n : ℚ)) • tpow (ν.erase n) := by sorry
