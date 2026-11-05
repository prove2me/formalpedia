-- Prove2me | Theorems.Thm_GeneralPieces_GenF_wtX_xo
-- name    : GeneralPieces.GenF.wtX_xo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:13:29.355266+00:00
-- url     : https://prove2.me/theorems/4a9bb97b-ad3b-49c7-850c-a9a1093e7290
-- title:
--   Gen F: wt X xo
-- statement:
--   The Gen F construction uses the wt X xo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Kappa.lean#L42-L44
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Kappa.lean#L42-L44

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

theorem GeneralPieces.GenF.wtX_xo (rd : Bool) (n : ℕ) : wtX (Finsupp.single (xo rd n) 1) = n := by sorry
