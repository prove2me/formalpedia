-- Prove2me | Theorems.Thm_GeneralPieces_GenF_pderiv_GG_xo
-- name    : GeneralPieces.GenF.pderiv_GG_xo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:12:28.014619+00:00
-- url     : https://prove2.me/theorems/76ce5ad7-25d7-45b5-a373-ca81eeb884ea
-- title:
--   Gen F: pderiv GG xo
-- statement:
--   The derivative with respect to a variable of the outer family falls on w.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Y2.lean#L112-L119
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Y2.lean#L112-L119

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

theorem GeneralPieces.GenF.pderiv_GG_xo (rd : Bool) (E : ℕ) (σ : Multiset ℕ) (n : ℕ) (w : W) :
    MvPowerSeries.pderiv S (xo rd n) (GG rd E σ w) = GG rd E σ (MvPowerSeries.pderiv Tv (xo rd n) w) := by sorry
