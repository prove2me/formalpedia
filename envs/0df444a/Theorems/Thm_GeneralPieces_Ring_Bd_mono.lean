-- Prove2me | Theorems.Thm_GeneralPieces_Ring_Bd_mono
-- name    : GeneralPieces.Ring.Bd.mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:26:39.228709+00:00
-- url     : https://prove2.me/theorems/c1fbf0f2-76b4-428a-a7c5-9a1a83a28ee0
-- title:
--   Bd: mono
-- statement:
--   The Bd construction uses the mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/OpFacts.lean#L66-L66
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/OpFacts.lean#L66-L66

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Basic
import Definitions.Def_GeneralPieces_Ring_OpFacts
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Ring
open AppHalfPieces MvPolynomial Finset

theorem GeneralPieces.Ring.Bd.mono {f : V} {E E' : ℤ} (h : Bd f E) (hE : E ≤ E') : Bd f E' := by sorry
