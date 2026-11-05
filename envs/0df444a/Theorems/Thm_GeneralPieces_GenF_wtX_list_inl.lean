-- Prove2me | Theorems.Thm_GeneralPieces_GenF_wtX_list_inl
-- name    : GeneralPieces.GenF.wtX_list_inl
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:13:40.491199+00:00
-- url     : https://prove2.me/theorems/f828f080-1979-4f86-bc89-48f6c86650c8
-- title:
--   Gen F: wt X list inl
-- statement:
--   The Gen F construction uses the wt X list inl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Kappa.lean#L57-L57
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Kappa.lean#L57-L57

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Defs
import Definitions.Def_GeneralPieces_GenF_Exp
import Definitions.Def_GeneralPieces_GenF_Kappa
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson MvPowerSeries Finset

theorem GeneralPieces.GenF.wtX_list_inl (a : List ℕ) : wtX (a.map fun n => Finsupp.single (Sum.inl n : X) 1).sum = a.sum := by sorry
