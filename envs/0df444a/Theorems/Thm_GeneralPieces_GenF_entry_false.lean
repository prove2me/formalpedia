-- Prove2me | Theorems.Thm_GeneralPieces_GenF_entry_false
-- name    : GeneralPieces.GenF.entry_false
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:14:10.710191+00:00
-- url     : https://prove2.me/theorems/88297820-f801-4956-9e5a-ac3b983f6836
-- title:
--   Gen F: entry false
-- statement:
--   One entry of the bilinear form κ, first reading.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Kappa.lean#L117-L133
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Kappa.lean#L117-L133

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

theorem GeneralPieces.GenF.entry_false {α : X →₀ ℕ} (hα : α.degree = 2) {i i' : X} (hi : i ∈ α.support) (hi' : i' ∈ α.support) :
    sel false (fun p => sel false 0 (fun q => kapS p q) i') 0 i = algebraMap ℚ S (GamX i i') * epsP ^ wtX α := by sorry
