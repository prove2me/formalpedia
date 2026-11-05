-- Prove2me | Theorems.Thm_GeneralPieces_GenF_Y_pderiv_ket
-- name    : GeneralPieces.GenF.Y.pderiv_ket
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:34:33.937918+00:00
-- url     : https://prove2.me/theorems/561ec7c4-e76d-475f-8cac-5569a7c25e62
-- title:
--   Y: pderiv ket
-- statement:
--   ∂/∂x_i of e^{B⁻}·t^σ': one of the factors is differentiated.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Y.lean#L142-L146
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Y.lean#L142-L146

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Borel
import Definitions.Def_GeneralPieces_GenF_NormalL
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_GeneralPieces_GenF_Y
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson MvPowerSeries
open Y
open GeneralPieces.GenF.Y

theorem GeneralPieces.GenF.Y.pderiv_ket (rd : Bool) (i : X) (σ' : Multiset ℕ) :
    pderiv Tv i (ket rd σ') = ∑ k ∈ σ'.toFinset, C (emb (((k : ℚ) * σ'.count k) • cB rd k i)) * ket rd (σ'.erase k) := by sorry
