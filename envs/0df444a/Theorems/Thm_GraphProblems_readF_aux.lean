-- Prove2me | Theorems.Thm_GraphProblems_readF_aux
-- name    : GraphProblems.readF_aux
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T20:58:53.699854+00:00
-- url     : https://prove2.me/theorems/528e8088-a30a-47c7-9465-16ccdb55fe35
-- title:
--   Graph Problems: read F aux
-- statement:
--   The Graph Problems construction uses the read F aux property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/GraphProblems/SetTM.lean#L47-L51
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/GraphProblems/SetTM.lean#L47-L51

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GraphProblems_Interfaces
import Definitions.Def_GraphProblems_Host
import Definitions.Def_GraphProblems_Cert
import Definitions.Def_ToTuring_Poly_Basic
import Mathlib.Tactic
import Definitions.Def_GraphProblems_SetTM
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
open GraphProblems
open Groundwork Groundwork.Prog Groundwork.Stepped CountKSat Turing

theorem GraphProblems.readF_aux {r : List Bool → List Unit × ℕ × List Bool} (hr : PolyT r) {F : ℕ → List Bool → Fml}
    (hF : PolyT fun a : List Unit × List Bool => F a.1.length a.2) : PolyT fun x => ((r x).1, (r x).2.1, F (r x).1.length (r x).2.2) := by sorry
