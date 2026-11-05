-- Prove2me | Theorems.Thm_GraphProblems_readF_polyT
-- name    : GraphProblems.readF_polyT
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T20:59:14.453782+00:00
-- url     : https://prove2.me/theorems/c7861cee-8491-4aa5-80db-d55f42a3b4c2
-- title:
--   Graph Problems: read F poly T
-- statement:
--   The Graph Problems construction uses the read F poly T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/GraphProblems/SetTM.lean#L53-L54
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/GraphProblems/SetTM.lean#L53-L54

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

theorem GraphProblems.readF_polyT (hR : StCertRead) {F : ℕ → List Bool → Fml} (hF : PolyT fun a : List Unit × List Bool => F a.1.length a.2) :
    PolyT (readF F) := by sorry
