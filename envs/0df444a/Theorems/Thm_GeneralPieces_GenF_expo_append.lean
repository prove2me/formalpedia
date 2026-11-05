-- Prove2me | Theorems.Thm_GeneralPieces_GenF_expo_append
-- name    : GeneralPieces.GenF.expo_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:08:48.914916+00:00
-- url     : https://prove2.me/theorems/3b43fe4e-c871-4e76-ae04-e74baa73d80d
-- title:
--   Gen F: expo append
-- statement:
--   The Gen F construction uses the expo append property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Borel.lean#L33-L33
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Borel.lean#L33-L33

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

theorem GeneralPieces.GenF.expo_append (L L' : List Y) : expo (L ++ L') = expo L + expo L' := by sorry
