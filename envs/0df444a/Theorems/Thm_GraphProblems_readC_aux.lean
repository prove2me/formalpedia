-- Prove2me | Theorems.Thm_GraphProblems_readC_aux
-- name    : GraphProblems.readC_aux
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:11:26.223702+00:00
-- url     : https://prove2.me/theorems/633c8eb8-7ea0-4a34-b823-635478fa1b58
-- title:
--   Graph Problems: read C aux
-- statement:
--   The Graph Problems construction uses the read C aux property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/GraphProblems/ColorTM.lean#L29-L35
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/GraphProblems/ColorTM.lean#L29-L35

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GraphProblems_Interfaces
import Definitions.Def_GraphProblems_Host
import Definitions.Def_GraphProblems_Engine
import Definitions.Def_GraphProblems_Sized
import Definitions.Def_GraphProblems_SetTM
import Mathlib.Tactic
import Definitions.Def_GraphProblems_ColorTM
import Theorems.Thm_Groundwork_PolyT_dedup
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.dedup
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
open GraphProblems
open Groundwork Groundwork.Prog Groundwork.Stepped CountKSat Turing

theorem GraphProblems.readC_aux (k : ℕ) {r : List Bool → List Unit × List Bool} (hr : PolyT r)
    (hF : PolyT fun a : List Unit × List Bool => colorF k a.1.length a.2) :
    PolyT fun x => (List.replicate ((r x).1.length * k) (), (colorF k (r x).1.length (r x).2).dedup) := by sorry
