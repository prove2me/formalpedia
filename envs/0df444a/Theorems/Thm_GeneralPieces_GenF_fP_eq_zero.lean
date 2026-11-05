-- Prove2me | Theorems.Thm_GeneralPieces_GenF_fP_eq_zero
-- name    : GeneralPieces.GenF.fP_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:16:08.981636+00:00
-- url     : https://prove2.me/theorems/c91f2a4a-f578-4304-8558-56863ff82876
-- title:
--   Gen F: f P eq zero
-- statement:
--   So f₊ = 0 if the two monomials have different weights. The paper takes both of weight E.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Assemble.lean#L112-L118
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Assemble.lean#L112-L118

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

theorem GeneralPieces.GenF.fP_eq_zero (a b : List ℕ) {π σ : Multiset ℕ} (hne : π.sum ≠ σ.sum) : fP a b π σ = 0 := by sorry
