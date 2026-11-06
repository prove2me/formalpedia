-- Prove2me | Theorems.Thm_GraphProblems_nbhd_polyT
-- name    : GraphProblems.nbhd_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:57:44.677752+00:00
-- url     : https://prove2.me/theorems/06c5551c-312a-4e2f-8d98-93b79ee43cfa
-- title:
--   Graph Problems: nbhd poly T
-- statement:
--   The Graph Problems construction uses the nbhd poly T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/GraphProblems/Cert.lean#L71-L75
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/GraphProblems/Cert.lean#L71-L75

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

theorem GraphProblems.nbhd_polyT {n : α → ℕ} {m : α → List Bool} (hn : Unary n) (hm : PolyT m) : PolyT fun a => nbhd (n a) (m a) := by sorry
