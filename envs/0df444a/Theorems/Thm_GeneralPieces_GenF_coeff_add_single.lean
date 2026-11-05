-- Prove2me | Theorems.Thm_GeneralPieces_GenF_coeff_add_single
-- name    : GeneralPieces.GenF.coeff_add_single
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:33:36.593841+00:00
-- url     : https://prove2.me/theorems/94af5329-7d21-484e-bb77-420028577cda
-- title:
--   Gen F: coeff add single
-- statement:
--   A coefficient from the derivative: (γ_i + 1) times the coefficient at γ + x_i is the coefficient
--   of the derivative at γ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/NormalL.lean#L56-L59
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/NormalL.lean#L56-L59

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Products
import Definitions.Def_GeneralPieces_GenF_Bra
import Definitions.Def_GeneralPieces_GenF_NormalL
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson

theorem GeneralPieces.GenF.coeff_add_single (F : PS) (γ : X →₀ ℕ) (i : X) :
    MvPowerSeries.coeff (γ + Finsupp.single i 1) F = ((γ i : ℚ) + 1)⁻¹ • MvPowerSeries.coeff γ (MvPowerSeries.pderiv S i F) := by sorry
