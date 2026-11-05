-- Prove2me | Theorems.Thm_GeneralPieces_Dual_nabla_smul
-- name    : GeneralPieces.Dual.nabla_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:35:48.538203+00:00
-- url     : https://prove2.me/theorems/bd67d5e1-4c24-44d1-b185-d963b1694f2a
-- title:
--   Dual: nabla smul
-- statement:
--   ∇_k is linear.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Dual.lean#L370-L375
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Dual.lean#L370-L375

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_ClauseBound_Boson_Dual
import Definitions.Def_GeneralPieces_Ring_Dual
import Theorems.Thm_GeneralPieces_Ring_nabla_smul

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Dual
open Finset MvPolynomial AppHalfPieces

theorem GeneralPieces.Dual.nabla_smul (k : ℤ) (q : ℚ) (f : V) : nabla k (q • f) = q • nabla k f := by sorry
