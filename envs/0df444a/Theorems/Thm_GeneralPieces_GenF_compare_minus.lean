-- Prove2me | Theorems.Thm_GeneralPieces_GenF_compare_minus
-- name    : GeneralPieces.GenF.compare_minus
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:16:44.224069+00:00
-- url     : https://prove2.me/theorems/a273b54d-677c-4cea-805b-37204bfb151e
-- title:
--   Gen F: compare minus
-- statement:
--   Comparing the coefficients of x^μ·x'^ν in the second half.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Assemble.lean#L127-L130
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Assemble.lean#L127-L130

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

theorem GeneralPieces.GenF.compare_minus (h15 : StTwoOrders) (hY : StY) {a b : List ℕ} (ha : Pos a) (hb : Pos b) {π σ : Multiset ℕ} (hπ : 0 ∉ π) (hσ : 0 ∉ σ) (hw : π.sum = σ.sum)
    {E : ℕ} (hE : π.sum ≤ E) : fM a b π σ = fac (ex a b) • ∑ p ∈ antidiagonal (ex a b), (gam p.1 • epsM ^ wtX p.1) * coeff p.2 (normal true E π σ) := by sorry
