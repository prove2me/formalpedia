-- Prove2me | Theorems.Thm_FromPrinted_Consequences_nsethFrom
-- name    : FromPrinted.Consequences.nsethFrom
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:26:09.836829+00:00
-- url     : https://prove2.me/theorems/3d7c8989-97f8-43cc-9f1c-a5f5aff24194
-- title:
--   Consequences: nseth From
-- statement:
--   **«NSETH … is false as well»** (the sentence after Corollary 5), for Turing machines and
--   nondeterministic time in verifier form (`Eight.NSETH_TM`), from the two statements that name the
--   machines, as hypotheses: the machine for k-SAT is that of `StSmallWidths` for k ≤ 3 and that of
--   `StVerifier` for k > 3.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FromPrinted/Verifier.lean#L72-L78
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FromPrinted/Verifier.lean#L72-L78

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

theorem FromPrinted.Consequences.nsethFrom (hV : StVerifier) (hS : StSmallWidths) : NsethFalse := by sorry
