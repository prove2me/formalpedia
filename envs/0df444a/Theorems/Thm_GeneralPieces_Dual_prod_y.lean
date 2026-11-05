-- Prove2me | Theorems.Thm_GeneralPieces_Dual_prod_y
-- name    : GeneralPieces.Dual.prod_y
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:35:23.803177+00:00
-- url     : https://prove2.me/theorems/a70cd4b6-e9f0-4c6f-bd44-d9f22c75f17d
-- title:
--   Dual: prod y
-- statement:
--   «Multiplying out ∏ y_{μ_i}»: the sum over all choices of j_i ∈ {1, …, μ_i} of ∏ C(μ_i, j_i)
--   times the monomial ∏ t_{j_i}.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Dual.lean#L180-L189
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Dual.lean#L180-L189

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

theorem GeneralPieces.Dual.prod_y (μ : List ℕ+) : (μ.map y).prod = ∑ js ∈ tuples (μ.map fun n : ℕ+ => Icc 1 (n : ℕ)),
    (List.zipWith (fun (n : ℕ+) (j : ℕ) => ((n : ℕ).choose j : ℚ)) μ js).prod • tpow ((js.map Nat.toPNat' : List ℕ+) : Multiset ℕ+) := by sorry
