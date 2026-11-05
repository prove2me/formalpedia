-- Prove2me | Theorems.Thm_GeneralPieces_GenF_constantCoeff_GG
-- name    : GeneralPieces.GenF.constantCoeff_GG
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:12:39.809465+00:00
-- url     : https://prove2.me/theorems/ac547b07-693a-4166-9e32-763bbb456fe4
-- title:
--   Gen F: constant Coeff GG
-- statement:
--   The Gen F construction uses the constant Coeff GG property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Y2.lean#L129-L130
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Y2.lean#L129-L130

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

theorem GeneralPieces.GenF.constantCoeff_GG (rd : Bool) (E : ℕ) (σ : Multiset ℕ) (w : W) : MvPowerSeries.constantCoeff (GG rd E σ w) = bra σ (MvPowerSeries.constantCoeff w) := by sorry
