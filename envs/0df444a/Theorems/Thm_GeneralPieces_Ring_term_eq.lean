-- Prove2me | Theorems.Thm_GeneralPieces_Ring_term_eq
-- name    : GeneralPieces.Ring.term_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:28:02.59129+00:00
-- url     : https://prove2.me/theorems/90d17ba2-65e4-461e-a352-fcfb6c6ef40a
-- title:
--   Ring: term eq
-- statement:
--   The Ring construction uses the term eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Bridge.lean#L119-L119
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Bridge.lean#L119-L119

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

theorem GeneralPieces.Ring.term_eq (μ : List ℕ+) (ks : List ℤ) (f : V) : term μ ks f = ((wtQ μ ks : ℤ) : ℚ) • nordQ ks f := by sorry
