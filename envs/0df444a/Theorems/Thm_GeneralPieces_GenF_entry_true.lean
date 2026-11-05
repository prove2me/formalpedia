-- Prove2me | Theorems.Thm_GeneralPieces_GenF_entry_true
-- name    : GeneralPieces.GenF.entry_true
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:14:13.793255+00:00
-- url     : https://prove2.me/theorems/72e758a7-1e45-4309-8099-18f0b844321d
-- title:
--   Gen F: entry true
-- statement:
--   One entry of the bilinear form κ, second reading.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Kappa.lean#L136-L160
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Kappa.lean#L136-L160

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

theorem GeneralPieces.GenF.entry_true {α : X →₀ ℕ} (hα : α.degree = 2) {i i' : X} (hi : i ∈ α.support) (hi' : i' ∈ α.support) :
    sel true (fun p => sel true 0 (fun q => kapS p q) i') 0 i = algebraMap ℚ S (GamX i' i) * epsM ^ wtX α := by sorry
