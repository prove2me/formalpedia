-- Prove2me | Theorems.Thm_Groundwork_Prog_Count_litAt_polyT
-- name    : Groundwork.Prog.Count.litAt_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:49:44.786509+00:00
-- url     : https://prove2.me/theorems/4780a0db-39de-42b1-af81-4ca2afa067db
-- title:
--   Count: lit At poly T
-- statement:
--   The Count construction uses the lit At poly T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/Count.lean#L30-L32
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/Count.lean#L30-L32

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

theorem Groundwork.Prog.Count.litAt_polyT {φ : α → Fml} {i : α → ℕ} (hφ : PolyT φ) (hi : PolyT i) :
    PolyT fun x => litAt k (φ x) (i x) := by sorry
