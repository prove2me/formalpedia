-- Prove2me | Theorems.Thm_GeneralPieces_GenF_constantCoeff_embW_kap
-- name    : GeneralPieces.GenF.constantCoeff_embW_kap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:07:04.498721+00:00
-- url     : https://prove2.me/theorems/927119ce-cc3a-4cb3-aa15-6a4df7c5d17c
-- title:
--   Gen F: constant Coeff emb W kap
-- statement:
--   The Gen F construction uses the constant Coeff emb W kap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Commute.lean#L131-L132
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Commute.lean#L131-L132

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Products
import Definitions.Def_GeneralPieces_GenF_Bra
import Definitions.Def_GeneralPieces_GenF_Commute
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson LaurentPolynomial
open MvPowerSeries hiding C X

theorem GeneralPieces.GenF.constantCoeff_embW_kap (rd : Bool) : constantCoeff (embW (kap rd)) = 0 := by sorry
