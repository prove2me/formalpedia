-- Prove2me | Theorems.Thm_GeneralPieces_Dual_sum_coeff
-- name    : GeneralPieces.Dual.sum_coeff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:35:24.692518+00:00
-- url     : https://prove2.me/theorems/08a6018a-ace2-46ff-b8d5-442400b805dc
-- title:
--   Dual: sum coeff
-- statement:
--   The sum over the j_i of the coefficients is ∏ ϑ_{μ_i}(k_i).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Dual.lean#L204-L226
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Dual.lean#L204-L226

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

theorem GeneralPieces.Dual.sum_coeff (μ : List ℕ+) (ks : List ℤ) (hl : ks.length = μ.length) :
    ∑ js ∈ tuples (μ.map fun n : ℕ+ => Icc 1 (n : ℕ)), (List.zipWith (fun (n : ℕ+) (j : ℕ) => ((n : ℕ).choose j : ℚ)) μ js).prod *
      (((List.zipWith (fun (m : ℕ+) (k : ℤ) => binom (-k - 1) ((m : ℤ) - 1)) (js.map Nat.toPNat') ks).prod : ℤ) : ℚ) =
    (((List.zipWith theta μ ks).prod : ℤ) : ℚ) := by sorry
