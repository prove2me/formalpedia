-- Prove2me | Theorems.Thm_GeneralPieces_GenF_coeff_smul_mo_mul
-- name    : GeneralPieces.GenF.coeff_smul_mo_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:12:46.355325+00:00
-- url     : https://prove2.me/theorems/dedaee07-57e9-4664-99e4-c5e5ea3e4ee7
-- title:
--   Gen F: coeff smul mo mul
-- statement:
--   The Gen F construction uses the coeff smul mo mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Y2.lean#L143-L145
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Y2.lean#L143-L145

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

theorem GeneralPieces.GenF.coeff_smul_mo_mul (q : ℚ) (x : ℤ) (f : S) (y : ℤ) : ((q • mo x 0) * f).coeff y = (C q * T x) * f.coeff y := by sorry
