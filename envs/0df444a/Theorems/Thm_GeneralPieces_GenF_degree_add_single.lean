-- Prove2me | Theorems.Thm_GeneralPieces_GenF_degree_add_single
-- name    : GeneralPieces.GenF.degree_add_single
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:26:26.510083+00:00
-- url     : https://prove2.me/theorems/ce079108-6493-4b38-8aa5-4a08a2f046f7
-- title:
--   Gen F: degree add single
-- statement:
--   The Gen F construction uses the degree add single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/PDeriv.lean#L25-L26
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/PDeriv.lean#L25-L26

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Taylor
import Mathlib.RingTheory.MvPowerSeries.Derivative
import Definitions.Def_GeneralPieces_GenF_PDeriv
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open Finset MvPowerSeries
variable {X A : Type} [CommRing A] [Algebra ℚ A]

theorem GeneralPieces.GenF.degree_add_single (α : X →₀ ℕ) (i : X) : (α + Finsupp.single i 1).degree = α.degree + 1 := by sorry
