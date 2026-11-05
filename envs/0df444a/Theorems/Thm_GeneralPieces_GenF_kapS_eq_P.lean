-- Prove2me | Theorems.Thm_GeneralPieces_GenF_kapS_eq_P
-- name    : GeneralPieces.GenF.kapS_eq_P
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:13:50.447866+00:00
-- url     : https://prove2.me/theorems/824b85a1-8c7e-493b-86aa-59c922beb798
-- title:
--   Gen F: kap S eq P
-- statement:
--   The sum over k in the first reading: Γ_{p,q}·ε₊^{p+q}.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Kappa.lean#L100-L100
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Kappa.lean#L100-L100

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

theorem GeneralPieces.GenF.kapS_eq_P {p q : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q) : kapS p q = (Gam p q : ℚ) • epsP ^ (p + q) := by sorry
