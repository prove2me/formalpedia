-- Prove2me | Theorems.Thm_GeneralPieces_GenF_wtX_list_xo
-- name    : GeneralPieces.GenF.wtX_list_xo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:13:34.035738+00:00
-- url     : https://prove2.me/theorems/3b9902cf-da7b-4f17-8591-0ba7698d714b
-- title:
--   Gen F: wt X list xo
-- statement:
--   The Gen F construction uses the wt X list xo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Kappa.lean#L55-L55
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Kappa.lean#L55-L55

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

theorem GeneralPieces.GenF.wtX_list_xo (rd : Bool) (a : List ℕ) : wtX (a.map fun n => Finsupp.single (xo rd n) 1).sum = a.sum := by sorry
