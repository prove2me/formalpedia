-- Prove2me | Theorems.Thm_GeneralPieces_Dual_binom_symm
-- name    : GeneralPieces.Dual.binom_symm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:35:14.529215+00:00
-- url     : https://prove2.me/theorems/d9e32cbd-7cb5-4409-980e-1b7ec0878793
-- title:
--   Dual: binom symm
-- statement:
--   C(n, n−j) is the binomial coefficient of natural numbers C(n, j), for j ≤ n.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Dual.lean#L200-L201
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Dual.lean#L200-L201

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

theorem GeneralPieces.Dual.binom_symm (n j : ℕ) (h : j ≤ n) : binom n ((n : ℤ) - j) = (n.choose j : ℤ) := by sorry
