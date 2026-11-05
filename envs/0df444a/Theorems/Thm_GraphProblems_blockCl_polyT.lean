-- Prove2me | Theorems.Thm_GraphProblems_blockCl_polyT
-- name    : GraphProblems.blockCl_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:56:46.690207+00:00
-- url     : https://prove2.me/theorems/a6b94343-bfce-426a-b421-754ba8ed17bc
-- title:
--   Graph Problems: block Cl poly T
-- statement:
--   The Graph Problems construction uses the block Cl poly T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/GraphProblems/Cert.lean#L66-L67
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/GraphProblems/Cert.lean#L66-L67

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

theorem GraphProblems.blockCl_polyT (b : ℕ) {i d : α → ℕ} (hi : PolyT i) (hd : PolyT d) : PolyT fun a => blockCl b (i a) (d a) := by sorry
