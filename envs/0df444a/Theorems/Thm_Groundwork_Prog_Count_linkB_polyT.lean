-- Prove2me | Theorems.Thm_Groundwork_Prog_Count_linkB_polyT
-- name    : Groundwork.Prog.Count.linkB_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:50:13.385961+00:00
-- url     : https://prove2.me/theorems/1038ac76-005f-45d4-9abf-9251d4f34714
-- title:
--   Count: link B poly T
-- statement:
--   The Count construction uses the link B poly T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/Count.lean#L42-L44
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/Count.lean#L42-L44

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Poly_Spec
import Definitions.Def_ToTuring_Poly_IsPoly
import Definitions.Def_ToTuring_Lib_List3
import Definitions.Def_StepMachines_Prog_Count
import Definitions.Def_ToTuring_Poly_Count
set_option autoImplicit false
section
section
open Groundwork Groundwork.Prog Groundwork.Prog.Count
variable {α : Type} [Enc α] (g k : ℕ)

theorem Groundwork.Prog.Count.linkB_polyT {φ : α → Fml} {i i' : α → ℕ} (hφ : PolyT φ) (hi : PolyT i) (hi' : PolyT i') :
    PolyT fun x => linkB k (φ x) (i x) (i' x) := by sorry
