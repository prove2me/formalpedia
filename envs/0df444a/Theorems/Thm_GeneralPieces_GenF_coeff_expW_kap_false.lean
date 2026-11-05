-- Prove2me | Theorems.Thm_GeneralPieces_GenF_coeff_expW_kap_false
-- name    : GeneralPieces.GenF.coeff_expW_kap_false
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:15:29.047569+00:00
-- url     : https://prove2.me/theorems/d80024a1-8efa-4bfc-a8b0-ec37c4f7e9c2
-- title:
--   Gen F: coeff exp W kap false
-- statement:
--   The coefficient of x^{μ'}·x'^{ν'} in e^κ is Γ_{μ',ν'}·ε₊^{|μ'|+|ν'|}.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Kappa.lean#L187-L188
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Kappa.lean#L187-L188

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

theorem GeneralPieces.GenF.coeff_expW_kap_false (α : X →₀ ℕ) : coeff α (expW (kap false)) = gam α • epsP ^ wtX α := by sorry
