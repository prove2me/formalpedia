-- Prove2me | Theorems.Thm_GeneralPieces_GenF_eq_zero_of_wtX
-- name    : GeneralPieces.GenF.eq_zero_of_wtX
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:15:54.971731+00:00
-- url     : https://prove2.me/theorems/323c83d1-2fef-4f9b-908a-5a7e21b1b685
-- title:
--   Gen F: eq zero of wt X
-- statement:
--   A divisor of x^μ·x'^ν of weight 0 is 1, because all parts are positive.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Assemble.lean#L73-L86
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Assemble.lean#L73-L86

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

theorem GeneralPieces.GenF.eq_zero_of_wtX {a b : List ℕ} (ha : Pos a) (hb : Pos b) {γ : X →₀ ℕ} (hγ : γ ≤ ex a b) (h0 : wtX γ = 0) : γ = 0 := by sorry
