-- Prove2me | Theorems.Thm_GraphProblems_rest_polyT
-- name    : GraphProblems.rest_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:56:01.403303+00:00
-- url     : https://prove2.me/theorems/8b5ec788-36c3-4668-97df-f9f2bc8f0bf8
-- title:
--   Graph Problems: rest poly T
-- statement:
--   The Graph Problems construction uses the rest poly T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/GraphProblems/Cert.lean#L30-L30
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/GraphProblems/Cert.lean#L30-L30

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GraphProblems_Interfaces
import Definitions.Def_ToTuring_Poly_Sat
import Definitions.Def_CountKSat_Poly
import Definitions.Def_GraphProblems_Cert
set_option autoImplicit false
section
section
open GraphProblems
open Groundwork Groundwork.Prog CountKSat
variable {α : Type} [Enc α]

theorem GraphProblems.rest_polyT {x : α → List Bool} (hx : PolyT x) : PolyT fun a => rest (x a) := by sorry
