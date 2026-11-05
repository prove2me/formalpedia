-- Prove2me | Theorems.Thm_GeneralPieces_GenF_eq_add_single
-- name    : GeneralPieces.GenF.eq_add_single
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:27:48.802712+00:00
-- url     : https://prove2.me/theorems/8f686591-7a61-4300-b73d-e3441de3baa9
-- title:
--   Gen F: eq add single
-- statement:
--   A monomial of degree 2 in which two different variables occur is their product.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Kappa.lean#L62-L83
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Kappa.lean#L62-L83

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Defs
import Definitions.Def_GeneralPieces_GenF_Exp
import Definitions.Def_GeneralPieces_GenF_Kappa
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson MvPowerSeries Finset

theorem GeneralPieces.GenF.eq_add_single {α : X →₀ ℕ} (hα : α.degree = 2) {i i' : X} (hi : i ∈ α.support) (hi' : i' ∈ α.support) (hne : i ≠ i') :
    α = Finsupp.single i 1 + Finsupp.single i' 1 := by sorry
