-- Prove2me | Theorems.Thm_GeneralPieces_GenF_ex_true
-- name    : GeneralPieces.GenF.ex_true
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:15:41.061121+00:00
-- url     : https://prove2.me/theorems/540034c6-85f6-4f82-9e72-6738cb489c11
-- title:
--   Gen F: ex true
-- statement:
--   In the `true` case (the second order, Y(b,ω₂)·Y(a,ω₁)) the roles are exchanged: b enters through
--   `xi` and a through `xo`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Assemble.lean#L48-L48
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Assemble.lean#L48-L48

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

theorem GeneralPieces.GenF.ex_true (a b : List ℕ) : aL (xi true) b + aL (xo true) a = ex a b := by sorry
