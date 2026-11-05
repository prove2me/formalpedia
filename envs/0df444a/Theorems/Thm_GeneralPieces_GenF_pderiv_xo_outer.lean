-- Prove2me | Theorems.Thm_GeneralPieces_GenF_pderiv_xo_outer
-- name    : GeneralPieces.GenF.pderiv_xo_outer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:10:44.689114+00:00
-- url     : https://prove2.me/theorems/fa54456a-ee33-419c-9f42-47890ab0f777
-- title:
--   Gen F: pderiv xo outer
-- statement:
--   ∂/∂x'_n (e^{B⁺}e^{B⁻}·t^σ') = J_n^+(v)·e^{B⁺}e^{B⁻}·t^σ' + e^{B⁺}e^{B⁻}·J_n^-(v)·t^σ'.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Y.lean#L154-L162
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Y.lean#L154-L162

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

theorem GeneralPieces.GenF.pderiv_xo_outer (rd : Bool) {n : ℕ} (hn : 1 ≤ n) (σ' : Multiset ℕ) :
    pderiv Tv (xo rd n) (outer rd σ') = C (JpV n) * outer rd σ' +
      ∑ k ∈ σ'.toFinset, C (emb (((k : ℚ) * σ'.count k * bet n (-(k : ℤ))) • mo 0 (-(k : ℤ) - n))) * outer rd (σ'.erase k) := by sorry
