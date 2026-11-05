-- Prove2me | Theorems.Thm_GeneralPieces_GenF_pderiv_expD
-- name    : GeneralPieces.GenF.pderiv_expD
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:26:21.063436+00:00
-- url     : https://prove2.me/theorems/002eecca-5136-464e-92fa-24ee1c16818e
-- title:
--   Gen F: pderiv exp D
-- statement:
--   The same for commuting derivations.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/PDeriv.lean#L115-L117
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/PDeriv.lean#L115-L117

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

theorem GeneralPieces.GenF.pderiv_expD {D : X → Derivation ℚ A A} (hc : ∀ i j a, D i (D j a) = D j (D i a)) (i : X) (w : MvPowerSeries X A) :
    pderiv A i (expD D w) = expD D (pderiv A i w) + expD D (mapD (D i) w) := by sorry
