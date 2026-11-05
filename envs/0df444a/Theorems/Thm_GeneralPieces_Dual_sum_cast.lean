-- Prove2me | Theorems.Thm_GeneralPieces_Dual_sum_cast
-- name    : GeneralPieces.Dual.sum_cast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:35:33.184858+00:00
-- url     : https://prove2.me/theorems/d7c63394-4531-4bd6-a780-7912e3636432
-- title:
--   Dual: sum cast
-- statement:
--   |μ| as a sum of integers.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Dual.lean#L286-L291
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Dual.lean#L286-L291

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

theorem GeneralPieces.Dual.sum_cast (μ : List ℕ+) : (μ.map fun n : ℕ+ => (n : ℤ)).sum = (wt (μ : Multiset ℕ+) : ℤ) := by sorry
