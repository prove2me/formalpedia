-- Prove2me | Theorems.Thm_GeneralPieces_GenF_expo_cons
-- name    : GeneralPieces.GenF.expo_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:08:52.390609+00:00
-- url     : https://prove2.me/theorems/2961a842-ef26-4a58-8d68-6507671bbb86
-- title:
--   Gen F: expo cons
-- statement:
--   The Gen F construction uses the expo cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Borel.lean#L31-L31
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Borel.lean#L31-L31

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

theorem GeneralPieces.GenF.expo_cons (i : Y) (L : List Y) : expo (i :: L) = Finsupp.single i 1 + expo L := by sorry
