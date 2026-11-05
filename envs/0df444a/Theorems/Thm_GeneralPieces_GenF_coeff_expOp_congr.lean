-- Prove2me | Theorems.Thm_GeneralPieces_GenF_coeff_expOp_congr
-- name    : GeneralPieces.GenF.coeff_expOp_congr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:04:30.394899+00:00
-- url     : https://prove2.me/theorems/5ded0f93-6454-4fb9-bb82-566b49ea48a1
-- title:
--   Gen F: coeff exp Op congr
-- statement:
--   The coefficient of α in e^𝒪 f depends only on the coefficients of f at the monomials of degree
--   at most that of α.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Taylor.lean#L275-L284
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Taylor.lean#L275-L284

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

theorem GeneralPieces.GenF.coeff_expOp_congr (O : X → A →ₗ[ℚ] A) (α : X →₀ ℕ) (f g : MvPowerSeries X A) (h : ∀ β : X →₀ ℕ, β.degree ≤ α.degree → coeff β f = coeff β g) :
    coeff α (expOp O f) = coeff α (expOp O g) := by sorry
