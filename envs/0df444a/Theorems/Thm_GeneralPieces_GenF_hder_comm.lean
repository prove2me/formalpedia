-- Prove2me | Theorems.Thm_GeneralPieces_GenF_hder_comm
-- name    : GeneralPieces.GenF.hder_comm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:04:47.827146+00:00
-- url     : https://prove2.me/theorems/7104b9bf-f3fb-42a4-a9ff-c733187f67d9
-- title:
--   Gen F: hder comm
-- statement:
--   Commuting derivations give commuting derivations.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Hahn.lean#L58-L60
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Hahn.lean#L58-L60

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

theorem GeneralPieces.GenF.hder_comm {d d' : Derivation ℚ A A} (h : ∀ a, d (d' a) = d' (d a)) (f : HahnSeries ℤ A) : hder d (hder d' f) = hder d' (hder d f) := by sorry
