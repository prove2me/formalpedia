-- Prove2me | Theorems.Thm_GeneralPieces_Ring_toN_erase
-- name    : GeneralPieces.Ring.toN_erase
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:30:10.222022+00:00
-- url     : https://prove2.me/theorems/f77dd39a-6558-4342-8ad5-b01f56c0bd38
-- title:
--   Ring: to N erase
-- statement:
--   The Ring construction uses the to N erase property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Bridge.lean#L145-L145
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Bridge.lean#L145-L145

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Defs
import Definitions.Def_ClauseBound_Boson_Text
import Mathlib.RingTheory.Derivation.Lie
import Definitions.Def_GeneralPieces_Ring_Bridge
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Ring
open AppHalfPieces MvPolynomial Finset

theorem GeneralPieces.Ring.toN_erase (π : Ptn) (l : ℕ+) : toN (π.erase l) = (toN π).erase (l : ℕ) := by sorry
