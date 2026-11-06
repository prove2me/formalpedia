-- Prove2me | Theorems.Thm_FromPrinted_Consequences_stSetsCounted
-- name    : FromPrinted.Consequences.stSetsCounted
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:23:51.891844+00:00
-- url     : https://prove2.me/theorems/6fe4c8bb-ecc0-48a2-8d79-7f37b25e6b7a
-- title:
--   Consequences: st Sets Counted
-- statement:
--   **Independent sets, cliques, vertex covers of size s, with the machines named.** For every δ > 0
--   there are ℓ, τ, c such that `SIZED 2 ℓ τ`, put after the reader of the formula for independent sets,
--   after `readClique` and after `readCover`, has polynomial-time steps and returns the three numbers
--   within c·2^{δn} steps, on states of size at most c·(n+2)^c.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FromPrinted/Sets.lean#L56-L69
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FromPrinted/Sets.lean#L56-L69

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FromPrinted_GraphDefs
import Definitions.Def_FromPrinted_Count
import Definitions.Def_Consequences_Sets
import Definitions.Def_SizeCircuit_Main
import Definitions.Def_Complement_Readers
import Definitions.Def_Eight_ViaGrouping_CorGraph
import Definitions.Def_GraphProblems_Read
import Definitions.Def_GraphProblems_Sets
import Definitions.Def_GraphProblems_Cert
import Definitions.Def_GraphProblems_SetTM
import Mathlib.Tactic
import Definitions.Def_FromPrinted_Sets
set_option autoImplicit false
section
section
open Consequences
open FromPrinted FromPrinted.Consequences
open Groundwork Groundwork.Prog CountKSat GraphProblems Paper Eight Eight.ViaGrouping FromPrinted.SplitCount SizeCircuit Complement

theorem FromPrinted.Consequences.stSetsCounted : StSetsCounted := by sorry
