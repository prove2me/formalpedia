-- Prove2me | Theorems.Thm_FromPrinted_Consequences_stSmallWidths
-- name    : FromPrinted.Consequences.stSmallWidths
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:33:46.975727+00:00
-- url     : https://prove2.me/theorems/c3b9a4e8-9bd7-484d-8c4e-9304b608739e
-- title:
--   Consequences: st Small Widths
-- statement:
--   For 1 ≤ k ≤ 3 and δ > 0 there are ℓ, τ, c such that `SATsmall k ℓ τ` has polynomial-time steps
--   and decides k-SAT with the exponent δ and the constant c.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FromPrinted/Verifier.lean#L52-L66
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FromPrinted/Verifier.lean#L52-L66

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FromPrinted_SatDefs
import Definitions.Def_FromPrinted_Core
import Definitions.Def_FromPrinted_SplitSat
import Definitions.Def_Eight_ViaGrouping_CorNSETH
import Definitions.Def_CountKSat_InOut
import Definitions.Def_WidthK_Decode
import Definitions.Def_FromPrinted_Verifier
set_option autoImplicit false
section
section
open Groundwork Groundwork.Prog CountKSat Paper Eight Eight.ViaGrouping
open SplitSat hiding core3 StCore3Eq StCore3 SATsplit StSATsplit StTiedTM StTiedThreeTM ThreeSatStatement
open FromPrinted.SplitSat
open FromPrinted FromPrinted.Consequences

theorem FromPrinted.Consequences.stSmallWidths : StSmallWidths := by sorry
