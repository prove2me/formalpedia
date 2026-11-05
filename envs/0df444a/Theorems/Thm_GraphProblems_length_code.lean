-- Prove2me | Theorems.Thm_GraphProblems_length_code
-- name    : GraphProblems.length_code
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:59:26.318198+00:00
-- url     : https://prove2.me/theorems/a4a03ab2-45c5-4b0f-b80e-fadf14617282
-- title:
--   Graph Problems: length code
-- statement:
--   The Graph Problems construction uses the length code property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/GraphProblems/SetTM.lean#L33-L34
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/GraphProblems/SetTM.lean#L33-L34

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

theorem GraphProblems.length_code (hL : StMatrixLength) {n : ℕ} (G : SimpleGraph (Fin n)) : (code G).length = n + 1 + n * n := by sorry
