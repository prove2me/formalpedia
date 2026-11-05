-- Prove2me | Theorems.Thm_GeneralPieces_GenF_pderiv_lin
-- name    : GeneralPieces.GenF.pderiv_lin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:26:51.326258+00:00
-- url     : https://prove2.me/theorems/beb77627-c4c5-4d43-85a3-32ed3354c380
-- title:
--   Gen F: pderiv lin
-- statement:
--   ∂/∂x_i Σ_v x_v·c_v = c_i.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Coeff.lean#L68-L77
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Coeff.lean#L68-L77

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_PDeriv
import Mathlib.Data.Finsupp.Multiset
import Definitions.Def_GeneralPieces_GenF_Coeff
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open Finset MvPowerSeries
variable {X A : Type} [CommRing A] [Algebra ℚ A]
omit [Algebra ℚ A]

theorem GeneralPieces.GenF.pderiv_lin (c : X → A) (i : X) : pderiv A i (lin c) = C (c i) := by sorry
