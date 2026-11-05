-- Prove2me | Theorems.Thm_GeneralPieces_GenF_ex_false
-- name    : GeneralPieces.GenF.ex_false
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:15:31.556455+00:00
-- url     : https://prove2.me/theorems/a449b7a6-c27d-490b-b1ef-955346cd4de8
-- title:
--   Gen F: ex false
-- statement:
--   In the `false` case (the first order, Y(a,ω₁)·Y(b,ω₂)) the parts of a enter through `xi` and
--   those of b through `xo`; the sum is the exponent of x^μ·x'^ν.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Assemble.lean#L44-L44
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Assemble.lean#L44-L44

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

theorem GeneralPieces.GenF.ex_false (a b : List ℕ) : aL (xi false) a + aL (xo false) b = ex a b := by sorry
