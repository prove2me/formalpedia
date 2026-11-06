-- Prove2me | Theorems.Thm_FromPrinted_Consequences_graphsByCounting
-- name    : FromPrinted.Consequences.graphsByCounting
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:42:09.915209+00:00
-- url     : https://prove2.me/theorems/7c4e8eac-5d2c-440b-b7dc-aaa0cc039782
-- title:
--   Consequences: graphs By Counting
-- statement:
--   **Corollary 7**, both sentences: `graphsFrom` on the proofs `stSetsCounted`,
--   `stDominatingCounted`, `stColoringsCounted`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FromPrinted/Circuits.lean#L110-L110
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FromPrinted/Circuits.lean#L110-L110

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FromPrinted_GraphDefs
import Definitions.Def_FromPrinted_Count
import Definitions.Def_FromPrinted_Sets
import Definitions.Def_FromPrinted_Dom
import Definitions.Def_Consequences_Main
import Definitions.Def_Eight_ViaGrouping_CorGraph
import Definitions.Def_Eight_ViaGrouping_CorENP
import Definitions.Def_GraphProblems_Host
import Definitions.Def_GraphProblems_SetTM
import Definitions.Def_SplitCount_Sizes
import Definitions.Def_GraphProblems_Read
import Definitions.Def_GraphProblems_Sets
import Definitions.Def_GraphProblems_Color
import Mathlib.Tactic
import Definitions.Def_FromPrinted_Circuits
set_option autoImplicit false
section
section
open Consequences
open FromPrinted FromPrinted.Consequences
open Groundwork Groundwork.Prog CountKSat GraphProblems Paper Eight Eight.ViaGrouping FromPrinted.SplitCount Turing

theorem FromPrinted.Consequences.graphsByCounting : GraphsByCounting := by sorry
