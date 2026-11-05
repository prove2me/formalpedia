-- Prove2me | Theorems.Thm_GeneralPieces_GenF_fM_eq_fP
-- name    : GeneralPieces.GenF.fM_eq_fP
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:34:27.454206+00:00
-- url     : https://prove2.me/theorems/632c64d9-da19-4f64-a286-8c0785262174
-- title:
--   Gen F: f M eq f P
-- statement:
--   f₋ is f₊ with the names exchanged.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Assemble.lean#L98-L100
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Assemble.lean#L98-L100

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

theorem GeneralPieces.GenF.fM_eq_fP (a b : List ℕ) (π σ : Multiset ℕ) : fM a b π σ = fP b a π σ := by sorry
