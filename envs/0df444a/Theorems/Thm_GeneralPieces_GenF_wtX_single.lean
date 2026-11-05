-- Prove2me | Theorems.Thm_GeneralPieces_GenF_wtX_single
-- name    : GeneralPieces.GenF.wtX_single
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:27:27.599531+00:00
-- url     : https://prove2.me/theorems/b613f303-e894-42f7-86ad-ff714e629914
-- title:
--   Gen F: wt X single
-- statement:
--   The Gen F construction uses the wt X single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Kappa.lean#L35-L36
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Kappa.lean#L35-L36

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

theorem GeneralPieces.GenF.wtX_single (i : X) (m : ℕ) : wtX (Finsupp.single i m) = m * Sum.elim id id i := by sorry
