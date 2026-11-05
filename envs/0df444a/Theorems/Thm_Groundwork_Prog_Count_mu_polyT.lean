-- Prove2me | Theorems.Thm_Groundwork_Prog_Count_mu_polyT
-- name    : Groundwork.Prog.Count.mu_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:49:41.842626+00:00
-- url     : https://prove2.me/theorems/b4cabd47-b4af-4f51-a20c-463a22a330b7
-- title:
--   Count: mu poly T
-- statement:
--   The Count construction uses the mu poly T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/Count.lean#L27-L28
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/Count.lean#L27-L28

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

theorem Groundwork.Prog.Count.mu_polyT {φ : α → Fml} (hφ : PolyT φ) : PolyT fun x => mu g (φ x) := by sorry
