-- Prove2me | Theorems.Thm_GeneralPieces_Ring_foldr_nabla_smul
-- name    : GeneralPieces.Ring.foldr_nabla_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:29:22.735764+00:00
-- url     : https://prove2.me/theorems/f449b561-8288-411b-bbb1-e477e3bceee5
-- title:
--   Ring: foldr nabla smul
-- statement:
--   The Ring construction uses the foldr nabla smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Bridge.lean#L99-L102
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Bridge.lean#L99-L102

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

theorem GeneralPieces.Ring.foldr_nabla_smul (l : List ℤ) (q : ℚ) (f : V) : l.foldr nabla (q • f) = q • l.foldr nabla f := by sorry
