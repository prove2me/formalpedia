-- Prove2me | Theorems.Thm_GeneralPieces_GenF_pderiv_prod
-- name    : GeneralPieces.GenF.pderiv_prod
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:34:24.571001+00:00
-- url     : https://prove2.me/theorems/017ece93-77b9-44d8-acfc-3ce166b37132
-- title:
--   Gen F: pderiv prod
-- statement:
--   The Gen F construction uses the pderiv prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Y2.lean#L102-L109
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Y2.lean#L102-L109

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

theorem GeneralPieces.GenF.pderiv_prod (rd : Bool) (E : ℕ) (i : X) (w : W) : MvPowerSeries.pderiv Tv i (expW (Ap rd E) * Phi rd w) =
    MvPowerSeries.C (sel rd (fun n => HahnSeries.C (JpU E n)) 0 i) * (expW (Ap rd E) * Phi rd w) +
      expW (Ap rd E) * (Phi rd (MvPowerSeries.pderiv Tv i w) + Phi rd (mapD (DD rd i) w)) := by sorry
