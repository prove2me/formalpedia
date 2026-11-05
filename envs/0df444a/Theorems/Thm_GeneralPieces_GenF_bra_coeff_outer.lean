-- Prove2me | Theorems.Thm_GeneralPieces_GenF_bra_coeff_outer
-- name    : GeneralPieces.GenF.bra_coeff_outer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:11:11.4332+00:00
-- url     : https://prove2.me/theorems/010e8d45-5949-4806-bf1d-096f89e5bbf0
-- title:
--   Gen F: bra coeff outer
-- statement:
--   "Expanding the exponentials gives e^{B⁺}e^{B⁻} = Σ_ν x'^ν·Y(t^ν, v)/ν!": ν! times the
--   coefficient of x'^ν in e^{B⁺}e^{B⁻}·t^σ' has, at t^τ, the coefficient ⟨τ|Y(t^ν, v)|σ'⟩.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Y.lean#L171-L182
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Y.lean#L171-L182

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

theorem GeneralPieces.GenF.bra_coeff_outer (rd : Bool) (b : List ℕ) (hb : Pos b) (τ σ' : Multiset ℕ) :
    bra τ (fac (aL (xo rd) b) • coeff (aL (xo rd) b) (outer rd σ')) = Yent (mo 0) b τ σ' := by sorry
