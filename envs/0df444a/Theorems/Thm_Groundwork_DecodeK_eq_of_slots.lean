-- Prove2me | Theorems.Thm_Groundwork_DecodeK_eq_of_slots
-- name    : Groundwork.DecodeK.eq_of_slots
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:23:29.779149+00:00
-- url     : https://prove2.me/theorems/ac4c4d1c-8614-41a8-9c17-1ee1eac3e15a
-- title:
--   Decode K: eq of slots
-- statement:
--   A clause of at most k literals is determined by its entries at the places 0 to k − 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/WidthK/Decode.lean#L50-L55
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/WidthK/Decode.lean#L50-L55

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_KSatStatement
import Definitions.Def_StepMachines_Prog_Decode
import Definitions.Def_StepMachines_Prog_Decode
import Definitions.Def_StepMachines_Prog_Decode
import Definitions.Def_StepMachines_Math_Formula
import Definitions.Def_StepMachines_Math_Formula
import Definitions.Def_WidthK_Decode
import Theorems.Thm_Sat3_eq_of_slots

set_option autoImplicit false
section
open Groundwork Groundwork.DecodeK
open Sat3 (Lit CNF Satisfiable slot)
open SatK
open Groundwork.Decode

theorem Groundwork.DecodeK.eq_of_slots {k n : ℕ} {C D : List (Lit n)} (hC : C.length ≤ k) (hD : D.length ≤ k)
    (h : ∀ j < k, C[j]? = D[j]?) : C = D := by sorry
