-- Prove2me | Theorems.Thm_GeneralPieces_GenF_coeff_expW_kap_true
-- name    : GeneralPieces.GenF.coeff_expW_kap_true
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:15:37.06049+00:00
-- url     : https://prove2.me/theorems/0423bac6-1fac-4551-a539-77dd7173d7ee
-- title:
--   Gen F: coeff exp W kap true
-- statement:
--   The coefficient of x^{μ'}·x'^{ν'} in e^{κ'} is Γ_{μ',ν'}·ε₋^{|μ'|+|ν'|}, with the same number.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Kappa.lean#L191-L192
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Kappa.lean#L191-L192

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

theorem GeneralPieces.GenF.coeff_expW_kap_true (α : X →₀ ℕ) : coeff α (expW (kap true)) = gam α • epsM ^ wtX α := by sorry
