-- Prove2me | Theorems.Thm_GeneralPieces_GenF_mul2_eq_zero_of_sum_ne
-- name    : GeneralPieces.GenF.mul2_eq_zero_of_sum_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:16:02.141078+00:00
-- url     : https://prove2.me/theorems/12170c68-5067-4785-8ce6-fe015d408bd7
-- title:
--   Gen F: mul2 eq zero of sum ne
-- statement:
--   A product a[r]∘b[−r] has no entries between monomials of different weights.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Assemble.lean#L103-L109
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Assemble.lean#L103-L109

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Products
import Definitions.Def_GeneralPieces_GenF_Kappa
import Definitions.Def_ClauseBound_Boson_Basic
import Mathlib.Data.Finsupp.Antidiagonal
import Mathlib.Data.Finsupp.Weight
import Definitions.Def_GeneralPieces_GenF_Assemble
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson MvPowerSeries Finset

theorem GeneralPieces.GenF.mul2_eq_zero_of_sum_ne (a b : List ℕ) {r r' : ℤ} (h : r + r' = 0) {π σ : Multiset ℕ} (hne : π.sum ≠ σ.sum) : mul2 a r b r' π σ = 0 := by sorry
