-- Prove2me | Theorems.Thm_GeneralPieces_GenF_Y_aL_cons
-- name    : GeneralPieces.GenF.Y.aL_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:10:28.386736+00:00
-- url     : https://prove2.me/theorems/58be31d4-77eb-4f6c-91f2-e60a1687cd4a
-- title:
--   Y: a L cons
-- statement:
--   The Y construction uses the a L cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Y.lean#L112-L113
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Y.lean#L112-L113

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Borel
import Definitions.Def_GeneralPieces_GenF_NormalL
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_GeneralPieces_GenF_Y
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson MvPowerSeries
open GeneralPieces.GenF.Y
variable {Z R : Type} [CommRing R] [Algebra ℚ R]

theorem GeneralPieces.GenF.Y.aL_cons (ι : ℕ → X) (n : ℕ) (a : List ℕ) : aL ι (n :: a) = aL ι a + Finsupp.single (ι n) 1 := by sorry
