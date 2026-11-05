-- Prove2me | Theorems.Thm_GeneralPieces_GenF_wtX_list_sum
-- name    : GeneralPieces.GenF.wtX_list_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:27:35.865065+00:00
-- url     : https://prove2.me/theorems/7f957a0a-a42e-46ef-9520-ea8fe8181248
-- title:
--   Gen F: wt X list sum
-- statement:
--   The weight of the monomial x^μ (or x'^μ) made from the list of the parts of μ is |μ|, if the
--   variable with index n has weight n.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Kappa.lean#L48-L51
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Kappa.lean#L48-L51

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

theorem GeneralPieces.GenF.wtX_list_sum (ι : ℕ → X) (hι : ∀ n, wtX (Finsupp.single (ι n) 1) = n) (a : List ℕ) : wtX (a.map fun n => Finsupp.single (ι n) 1).sum = a.sum := by sorry
