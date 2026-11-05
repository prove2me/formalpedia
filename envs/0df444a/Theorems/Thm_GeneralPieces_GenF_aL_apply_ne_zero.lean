-- Prove2me | Theorems.Thm_GeneralPieces_GenF_aL_apply_ne_zero
-- name    : GeneralPieces.GenF.aL_apply_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:15:45.5931+00:00
-- url     : https://prove2.me/theorems/423dccf6-9921-4ead-bbfa-c6ea1d3d366f
-- title:
--   Gen F: a L apply ne zero
-- statement:
--   Only the variables with an index in the list occur.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Assemble.lean#L55-L70
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Assemble.lean#L55-L70

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

theorem GeneralPieces.GenF.aL_apply_ne_zero {ι : ℕ → X} {a : List ℕ} {i : X} (h : aL ι a i ≠ 0) : ∃ n ∈ a, i = ι n := by sorry
