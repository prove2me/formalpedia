-- Prove2me | Theorems.Thm_FromPrinted_Consequences_nsethFalse
-- name    : FromPrinted.Consequences.nsethFalse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:45:38.417097+00:00
-- url     : https://prove2.me/theorems/1ee92f80-032e-4750-808a-e180254006e1
-- title:
--   Consequences: nseth False
-- statement:
--   **«NSETH … is false as well»**: `nsethFrom` on the proofs `stVerifier` and `stSmallWidths`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FromPrinted/Verifier.lean#L81-L81
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FromPrinted/Verifier.lean#L81-L81

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

theorem FromPrinted.Consequences.nsethFalse : NsethFalse := by sorry
