-- Prove2me | Theorems.Thm_Groundwork_Prog_Count_links_polyT
-- name    : Groundwork.Prog.Count.links_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:51:09.35436+00:00
-- url     : https://prove2.me/theorems/6a723793-a906-402e-8768-f7d277e6ed95
-- title:
--   Count: links poly T
-- statement:
--   The Count construction uses the links poly T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/Count.lean#L53-L57
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/Count.lean#L53-L57

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

theorem Groundwork.Prog.Count.links_polyT {φ : α → Fml} {a b : α → ℕ} (hφ : PolyT φ) (ha : PolyT a) (hb : PolyT b) :
    PolyT fun x => links g k (φ x) (a x) (b x) := by sorry
