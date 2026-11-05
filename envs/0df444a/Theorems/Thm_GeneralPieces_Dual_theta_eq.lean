-- Prove2me | Theorems.Thm_GeneralPieces_Dual_theta_eq
-- name    : GeneralPieces.Dual.theta_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:24:46.441203+00:00
-- url     : https://prove2.me/theorems/7ba473a0-9e2c-4d52-aed0-5cc5df1aeca5
-- title:
--   Dual: theta eq
-- statement:
--   «By Vandermonde's identity ϑ_n(k) = C(n−k−1, n−1)».
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Dual.lean#L36-L44
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Dual.lean#L36-L44

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

theorem GeneralPieces.Dual.theta_eq (n : ℕ+) (k : ℤ) : theta n k = binom ((n : ℤ) - k - 1) ((n : ℤ) - 1) := by sorry
