-- Prove2me | Theorems.Thm_GeneralPieces_GenF_pderiv_xi_outer
-- name    : GeneralPieces.GenF.pderiv_xi_outer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:10:50.857433+00:00
-- url     : https://prove2.me/theorems/f1f3b8d5-440f-4973-afda-1c498ba17d14
-- title:
--   Gen F: pderiv xi outer
-- statement:
--   The variables of the inner family do not occur in e^{B⁺}e^{B⁻}·t^σ'.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Y.lean#L165-L167
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Y.lean#L165-L167

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

theorem GeneralPieces.GenF.pderiv_xi_outer (rd : Bool) (n : ℕ) (σ' : Multiset ℕ) : pderiv Tv (xi rd n) (outer rd σ') = 0 := by sorry
