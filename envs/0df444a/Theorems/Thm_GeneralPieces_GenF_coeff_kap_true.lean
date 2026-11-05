-- Prove2me | Theorems.Thm_GeneralPieces_GenF_coeff_kap_true
-- name    : GeneralPieces.GenF.coeff_kap_true
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:15:11.664395+00:00
-- url     : https://prove2.me/theorems/ce355ec6-eac1-4d83-8268-d5aa1f6f7a65
-- title:
--   Gen F: coeff kap true
-- statement:
--   The coefficients of κ': those of Σ_{j,n} Γ_{j,n}·x_j·x'_n, times ε₋^{j+n}.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Kappa.lean#L176-L184
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Kappa.lean#L176-L184

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

theorem GeneralPieces.GenF.coeff_kap_true (α : X →₀ ℕ) : coeff α (kap true) = algebraMap ℚ S (coeff α kapQ) * epsM ^ wtX α := by sorry
