-- Prove2me | Theorems.Thm_GeneralPieces_Dual_theta_self
-- name    : GeneralPieces.Dual.theta_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:34:50.230196+00:00
-- url     : https://prove2.me/theorems/5d2c30b4-d09d-4531-80dd-8a0342e35044
-- title:
--   Dual: theta self
-- statement:
--   «… and (−1)^{n−1} for k = n.»
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Dual.lean#L63-L66
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Dual.lean#L63-L66

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

theorem GeneralPieces.Dual.theta_self (n : ℕ+) : theta n n = (-1) ^ ((n : ℕ) - 1) := by sorry
