-- Prove2me | Theorems.Thm_GraphProblems_digit_polyT
-- name    : GraphProblems.digit_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:55:11.150146+00:00
-- url     : https://prove2.me/theorems/9c29cfe7-14a8-4d5e-9ee3-4c6b1951a412
-- title:
--   Graph Problems: digit poly T
-- statement:
--   The Graph Problems construction uses the digit poly T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/GraphProblems/Cert.lean#L63-L64
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/GraphProblems/Cert.lean#L63-L64

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

theorem GraphProblems.digit_polyT (b : ℕ) {y i : α → ℕ} (hy : PolyT y) (hi : PolyT i) : PolyT fun a => digit b (y a) (i a) := by sorry
