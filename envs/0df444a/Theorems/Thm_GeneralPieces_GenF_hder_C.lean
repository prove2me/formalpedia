-- Prove2me | Theorems.Thm_GeneralPieces_GenF_hder_C
-- name    : GeneralPieces.GenF.hder_C
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:04:45.856219+00:00
-- url     : https://prove2.me/theorems/880a8232-4cd9-4588-a793-bdbf9c60eaa6
-- title:
--   Gen F: hder C
-- statement:
--   On a constant series.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Hahn.lean#L71-L71
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Hahn.lean#L71-L71

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Mathlib.RingTheory.HahnSeries.Multiplication
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.Module.Rat
import Definitions.Def_GeneralPieces_GenF_Hahn
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open Finset HahnSeries
variable {A : Type} [CommRing A] [Algebra ℚ A]

theorem GeneralPieces.GenF.hder_C (d : Derivation ℚ A A) (a : A) : hder d (HahnSeries.C a) = HahnSeries.C (d a) := by sorry
