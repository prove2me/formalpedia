-- Prove2me | Theorems.Thm_GraphProblems_bits_polyT
-- name    : GraphProblems.bits_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:59:26.294844+00:00
-- url     : https://prove2.me/theorems/baa9dbfd-f06b-458a-b850-eaa92f0dc434
-- title:
--   Graph Problems: bits poly T
-- statement:
--   The Graph Problems construction uses the bits poly T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/GraphProblems/SetTM.lean#L41-L41
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/GraphProblems/SetTM.lean#L41-L41

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GraphProblems_Interfaces
import Definitions.Def_GraphProblems_Host
import Definitions.Def_GraphProblems_Cert
import Definitions.Def_ToTuring_Poly_Basic
import Mathlib.Tactic
import Definitions.Def_GraphProblems_SetTM
set_option autoImplicit false
section
open GraphProblems
open Groundwork Groundwork.Prog Groundwork.Stepped CountKSat Turing

theorem GraphProblems.bits_polyT : PolyT Nat.bits := by sorry
