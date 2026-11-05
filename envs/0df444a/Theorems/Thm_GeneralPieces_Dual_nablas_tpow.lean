-- Prove2me | Theorems.Thm_GeneralPieces_Dual_nablas_tpow
-- name    : GeneralPieces.Dual.nablas_tpow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:36:14.845633+00:00
-- url     : https://prove2.me/theorems/ef018947-ea6f-4f98-a9a9-ec1ab2de61bb
-- title:
--   Dual: nablas tpow
-- statement:
--   The last sentence of the proof: for partitions μ, ν of the same number, ∏_i ∇_{μ_i} t^ν = z_μ·[μ =
--   ν].
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Dual.lean#L452-L459
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Dual.lean#L452-L459

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

theorem GeneralPieces.Dual.nablas_tpow (μ : List ℕ+) (ν : Ptn) (hw : wt (μ : Multiset ℕ+) = wt ν) :
    nablas (μ.map fun n : ℕ+ => (n : ℤ)) (tpow ν) = C (if (μ : Multiset ℕ+) = ν then (zz (μ : Multiset ℕ+) : ℚ) else 0) := by sorry
