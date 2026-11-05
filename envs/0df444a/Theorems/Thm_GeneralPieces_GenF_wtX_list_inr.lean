-- Prove2me | Theorems.Thm_GeneralPieces_GenF_wtX_list_inr
-- name    : GeneralPieces.GenF.wtX_list_inr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:13:41.189694+00:00
-- url     : https://prove2.me/theorems/d912223a-77fe-48dc-bbd4-668f020d3660
-- title:
--   Gen F: wt X list inr
-- statement:
--   The Gen F construction uses the wt X list inr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Kappa.lean#L59-L59
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Kappa.lean#L59-L59

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

theorem GeneralPieces.GenF.wtX_list_inr (a : List ℕ) : wtX (a.map fun n => Finsupp.single (Sum.inr n : X) 1).sum = a.sum := by sorry
