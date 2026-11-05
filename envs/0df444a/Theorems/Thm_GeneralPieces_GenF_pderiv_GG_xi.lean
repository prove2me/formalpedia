-- Prove2me | Theorems.Thm_GeneralPieces_GenF_pderiv_GG_xi
-- name    : GeneralPieces.GenF.pderiv_GG_xi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:12:35.338792+00:00
-- url     : https://prove2.me/theorems/575499c2-0557-4727-8f1b-68c067838bf9
-- title:
--   Gen F: pderiv GG xi
-- statement:
--   The derivative with respect to the variable x_n of the inner family: ⟨J_n^+·e^{A⁺}e^{A⁻}·w⟩ +
--   ⟨e^{A⁺}e^{A⁻}·J_n^-·w⟩, if w does not depend on x_n.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Y2.lean#L123-L127
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Y2.lean#L123-L127

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_DDComm
import Definitions.Def_GeneralPieces_GenF_Borel
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_Eth_16a5ce4_GeneralPieces_GenF_Y2_Definitions
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson LaurentPolynomial Finset

theorem GeneralPieces.GenF.pderiv_GG_xi (rd : Bool) {E : ℕ} {σ : Multiset ℕ} (hσ : σ.sum ≤ E) {n : ℕ} (hn : 1 ≤ n) {w : W} (hw : MvPowerSeries.pderiv Tv (xi rd n) w = 0) :
    MvPowerSeries.pderiv S (xi rd n) (GG rd E σ w) =
      ∑ l ∈ σ.toFinset, MvPowerSeries.C ((bet n l : ℚ) • mo ((l : ℤ) - n) 0) * GG rd E (σ.erase l) w + GG rd E σ (mapD (JmT n) w) := by sorry
