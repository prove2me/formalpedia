-- Prove2me | Theorems.Thm_GeneralPieces_GenF_inv_factorial_succ_mul
-- name    : GeneralPieces.GenF.inv_factorial_succ_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:26:16.889231+00:00
-- url     : https://prove2.me/theorems/88dc2079-319c-4d81-aeb9-9b91f1a950c8
-- title:
--   Gen F: inv factorial succ mul
-- statement:
--   The Gen F construction uses the inv factorial succ mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/PDeriv.lean#L28-L33
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/PDeriv.lean#L28-L33

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

theorem GeneralPieces.GenF.inv_factorial_succ_mul (n : ℕ) : (((n + 1).factorial : ℚ)⁻¹) * ((n + 1 : ℕ) : ℚ) = ((n.factorial : ℚ)⁻¹) := by sorry
