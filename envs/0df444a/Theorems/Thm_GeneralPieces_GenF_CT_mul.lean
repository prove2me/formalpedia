-- Prove2me | Theorems.Thm_GeneralPieces_GenF_CT_mul
-- name    : GeneralPieces.GenF.CT_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:12:22.147472+00:00
-- url     : https://prove2.me/theorems/3f9b019b-3e8d-42b0-bab8-3409359a703c
-- title:
--   Gen F: CT mul
-- statement:
--   The Gen F construction uses the CT mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Y2.lean#L51-L53
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Y2.lean#L51-L53

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

theorem GeneralPieces.GenF.CT_mul (q q' : ℚ) (x x' : ℤ) : (C q * T x : Lu) * (C q' * T x') = C (q * q') * T (x + x') := by sorry
