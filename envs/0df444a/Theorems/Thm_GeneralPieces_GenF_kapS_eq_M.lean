-- Prove2me | Theorems.Thm_GeneralPieces_GenF_kapS_eq_M
-- name    : GeneralPieces.GenF.kapS_eq_M
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:14:01.571532+00:00
-- url     : https://prove2.me/theorems/b0230602-e11d-4109-8a63-83255eb1f1c6
-- title:
--   Gen F: kap S eq M
-- statement:
--   The sum over k in the second reading, where p is the index of x'_p and q that of x_q:
--   Γ_{q,p}·ε₋^{q+p}.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Kappa.lean#L104-L106
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Kappa.lean#L104-L106

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

theorem GeneralPieces.GenF.kapS_eq_M {p q : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q) : kapS p q = (Gam q p : ℚ) • epsM ^ (q + p) := by sorry
