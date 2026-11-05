-- Prove2me | Theorems.Thm_Groundwork_SatNet_Consec_pred_unique
-- name    : Groundwork.SatNet.Consec.pred_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:42:51.695195+00:00
-- url     : https://prove2.me/theorems/16a2b5f4-11dc-468b-9e3c-0f3f5c30059b
-- title:
--   Consec: pred unique
-- statement:
--   A slot has at most one predecessor.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SatNet.lean#L55-L63
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SatNet.lean#L55-L63

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThreeSatStatement
import Definitions.Def_Groundwork_Net_Defs
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Definitions.Def_StepMachines_Math_SatNet
set_option autoImplicit false
section
open Groundwork Groundwork.SatNet
open Finset
variable {ι V : Type}
variable {idx : ι → ℕ} {lab : ι → Option V}

theorem Groundwork.SatNet.Consec.pred_unique (hidx : Function.Injective idx) {p p' q : ι}
    (h : Consec idx lab p q) (h' : Consec idx lab p' q) : p = p' := by sorry
