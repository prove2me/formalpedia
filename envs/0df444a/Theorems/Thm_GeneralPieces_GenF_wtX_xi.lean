-- Prove2me | Theorems.Thm_GeneralPieces_GenF_wtX_xi
-- name    : GeneralPieces.GenF.wtX_xi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:13:21.712484+00:00
-- url     : https://prove2.me/theorems/77a56335-590c-4472-8281-13b95c263f50
-- title:
--   Gen F: wt X xi
-- statement:
--   The Gen F construction uses the wt X xi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Kappa.lean#L38-L40
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Kappa.lean#L38-L40

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

theorem GeneralPieces.GenF.wtX_xi (rd : Bool) (n : ℕ) : wtX (Finsupp.single (xi rd n) 1) = n := by sorry
