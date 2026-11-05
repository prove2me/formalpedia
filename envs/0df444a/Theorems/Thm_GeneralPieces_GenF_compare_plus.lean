-- Prove2me | Theorems.Thm_GeneralPieces_GenF_compare_plus
-- name    : GeneralPieces.GenF.compare_plus
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:16:13.278084+00:00
-- url     : https://prove2.me/theorems/518fd3bc-c4b1-4231-b1aa-5776831c3a25
-- title:
--   Gen F: compare plus
-- statement:
--   Comparing the coefficients of x^μ·x'^ν in the first half of display (51).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Assemble.lean#L121-L124
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Assemble.lean#L121-L124

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

theorem GeneralPieces.GenF.compare_plus (h15 : StTwoOrders) (hY : StY) {a b : List ℕ} (ha : Pos a) (hb : Pos b) {π σ : Multiset ℕ} (hπ : 0 ∉ π) (hσ : 0 ∉ σ) (hw : π.sum = σ.sum)
    {E : ℕ} (hE : π.sum ≤ E) : fP a b π σ = fac (ex a b) • ∑ p ∈ antidiagonal (ex a b), (gam p.1 • epsP ^ wtX p.1) * coeff p.2 (normal false E π σ) := by sorry
