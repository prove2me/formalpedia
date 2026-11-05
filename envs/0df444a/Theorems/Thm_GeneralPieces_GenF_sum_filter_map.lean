-- Prove2me | Theorems.Thm_GeneralPieces_GenF_sum_filter_map
-- name    : GeneralPieces.GenF.sum_filter_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:16:45.859893+00:00
-- url     : https://prove2.me/theorems/2dac9ad7-60cf-4f9c-87d6-467679852738
-- title:
--   Gen F: sum filter map
-- statement:
--   A sum over the terms of a list that pass a test.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Assemble.lean#L135-L143
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Assemble.lean#L135-L143

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Products
import Definitions.Def_GeneralPieces_GenF_Kappa
import Definitions.Def_ClauseBound_Boson_Basic
import Mathlib.Data.Finsupp.Antidiagonal
import Mathlib.Data.Finsupp.Weight
import Definitions.Def_GeneralPieces_GenF_Assemble
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson MvPowerSeries Finset

theorem GeneralPieces.GenF.sum_filter_map {ι : Type} (l : List ι) (F : ι → ℚ × ℕ × L) (H : ℕ) :
    (((l.map F).filter fun c => c.2.1 = H).map fun c => c.1).sum = (l.map fun x => if (F x).2.1 = H then (F x).1 else 0).sum := by sorry
