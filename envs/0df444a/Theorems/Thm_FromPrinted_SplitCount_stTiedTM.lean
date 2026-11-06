-- Prove2me | Theorems.Thm_FromPrinted_SplitCount_stTiedTM
-- name    : FromPrinted.SplitCount.stTiedTM
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:11:34.400205+00:00
-- url     : https://prove2.me/theorems/7e54bec1-cb3a-43ab-bbd5-2b432913dd79
-- title:
--   Split Count: st Tied TM
-- statement:
--   **Tied to the machine, on Mathlib's Turing machines.** For every k ≥ 1 and δ > 0 there are ℓ, τ,
--   a Turing machine M with finite alphabets and numbers c, q such that `COUNTsplit k ℓ τ` has
--   polynomial-time steps and writes the number of satisfying assignments of a k-CNF on n variables
--   within c·2^{δn} steps on states of size at most c·(length + 1)^c;
--   M simulates it with the overhead q·(T+1)·(|x|+S+1)^q; and M counts the satisfying assignments of
--   k-CNFs within ⌊c·2^{δn}⌋ steps.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FromPrinted/Count.lean#L150-L164
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FromPrinted/Count.lean#L150-L164

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FromPrinted_CountDefs
import Definitions.Def_Printed_End
import Definitions.Def_SplitCount_StepOne
import Definitions.Def_SplitCount_Main
import Definitions.Def_SplitCount_Tree
import Definitions.Def_SplitCount_Suffices
import Definitions.Def_SplitCount_Cert
import Definitions.Def_SplitCount_Host
import Definitions.Def_CountKSat_Host
import Definitions.Def_CountKSat_InOut
import Definitions.Def_CountKSat_Poly
import Definitions.Def_CountKSat_EndLemmas
import Definitions.Def_Eight_SecPseudocode_Levels
import Definitions.Def_WidthK_Decode
import Mathlib.Tactic
import Definitions.Def_FromPrinted_Count
set_option autoImplicit false
section
section
open SplitCount
open FromPrinted FromPrinted.SplitCount
open Groundwork Groundwork.Prog Paper CountKSat Eight Eight.ViaGrouping Occ
open scoped NNReal

theorem FromPrinted.SplitCount.stTiedTM : StTiedTM := by sorry
