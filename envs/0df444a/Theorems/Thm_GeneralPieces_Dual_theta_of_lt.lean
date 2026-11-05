-- Prove2me | Theorems.Thm_GeneralPieces_Dual_theta_of_lt
-- name    : GeneralPieces.Dual.theta_of_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:34:45.763677+00:00
-- url     : https://prove2.me/theorems/11c9f85e-94a5-48ad-9985-b6804deea123
-- title:
--   Dual: theta of lt
-- statement:
--   «… which is 0 for 1 ≤ k < n».
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Dual.lean#L56-L60
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Dual.lean#L56-L60

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

theorem GeneralPieces.Dual.theta_of_lt (n : ℕ+) (k : ℤ) (h1 : 1 ≤ k) (h2 : k < n) : theta n k = 0 := by sorry
