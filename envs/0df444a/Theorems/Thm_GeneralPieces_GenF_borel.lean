-- Prove2me | Theorems.Thm_GeneralPieces_GenF_borel
-- name    : GeneralPieces.GenF.borel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:09:14.371995+00:00
-- url     : https://prove2.me/theorems/02d18467-a70f-4606-af1f-6ff9b4e5ff31
-- title:
--   Gen F: borel
-- statement:
--   The Gen F construction uses the borel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Borel.lean#L94-L99
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Borel.lean#L94-L99

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Coeff
import Definitions.Def_GeneralPieces_GenF_Borel
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open Finset MvPowerSeries
variable {Y R : Type} [CommRing R]
variable [Algebra ℚ R]

theorem GeneralPieces.GenF.borel (L : List Y) : ∀ (β : Y →₀ ℕ) (F : MvPowerSeries Y R), fac (β + expo L) • coeff (β + expo L) F = fac β • coeff β (pdL L F) := by sorry
