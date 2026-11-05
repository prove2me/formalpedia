-- Prove2me | Theorems.Thm_GeneralPieces_GenF_hder_single
-- name    : GeneralPieces.GenF.hder_single
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:04:46.05442+00:00
-- url     : https://prove2.me/theorems/1445a16a-f7af-45f4-b6ae-396e84468566
-- title:
--   Gen F: hder single
-- statement:
--   On a series with one term.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Hahn.lean#L63-L68
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Hahn.lean#L63-L68

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

theorem GeneralPieces.GenF.hder_single (d : Derivation ℚ A A) (y : ℤ) (a : A) : hder d (single y a) = single y (d a) := by sorry
