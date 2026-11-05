-- Prove2me | Theorems.Thm_GeneralPieces_Ring_coef_smul
-- name    : GeneralPieces.Ring.coef_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:28:21.912214+00:00
-- url     : https://prove2.me/theorems/8515fe45-3499-4781-ae45-0dfb9b5b3051
-- title:
--   Ring: coef smul
-- statement:
--   The Ring construction uses the coef smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Bridge.lean#L95-L97
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Bridge.lean#L95-L97

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Defs
import Definitions.Def_ClauseBound_Boson_Text
import Mathlib.RingTheory.Derivation.Lie
import Definitions.Def_GeneralPieces_Ring_Bridge
import Theorems.Thm_ClauseBound_Boson_Text_coef_smul

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Ring
open AppHalfPieces MvPolynomial Finset

theorem GeneralPieces.Ring.coef_smul (π : Ptn) (q : ℚ) (f : V) : coef π (q • f) = q * coef π f := by sorry
