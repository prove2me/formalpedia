-- Prove2me | Theorems.Thm_GeneralPieces_GenF_coeff_lin
-- name    : GeneralPieces.GenF.coeff_lin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:25:47.623662+00:00
-- url     : https://prove2.me/theorems/7fefcb6e-c330-4f75-833b-246e3a018dfb
-- title:
--   Gen F: coeff lin
-- statement:
--   The Gen F construction uses the coeff lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Taylor.lean#L301-L301
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Taylor.lean#L301-L301

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Exp
import Mathlib.Algebra.MvPolynomial.Derivation
import Definitions.Def_GeneralPieces_GenF_Taylor
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open Finset MvPowerSeries
variable {X A : Type} [CommRing A] [Algebra ℚ A]
omit [Algebra ℚ A]

theorem GeneralPieces.GenF.coeff_lin (b : X → A) (α : X →₀ ℕ) : coeff α (lin b) = if α.degree = 1 then ∑ v ∈ α.support, b v else 0 := by sorry
