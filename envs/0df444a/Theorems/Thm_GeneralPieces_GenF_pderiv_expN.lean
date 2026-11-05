-- Prove2me | Theorems.Thm_GeneralPieces_GenF_pderiv_expN
-- name    : GeneralPieces.GenF.pderiv_expN
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:04:47.566048+00:00
-- url     : https://prove2.me/theorems/21eea9cb-5f6d-4dcb-a303-dae6e78dbe06
-- title:
--   Gen F: pderiv exp N
-- statement:
--   ∂/∂x_i Σ_{n ≤ N} wⁿ/n! = (∂w/∂x_i)·Σ_{n < N} wⁿ/n!.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/PDeriv.lean#L36-L43
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/PDeriv.lean#L36-L43

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

theorem GeneralPieces.GenF.pderiv_expN (i : X) (N : ℕ) (w : MvPowerSeries X A) : pderiv A i (expN (N + 1) w) = pderiv A i w * expN N w := by sorry
