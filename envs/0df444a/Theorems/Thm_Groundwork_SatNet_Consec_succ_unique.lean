-- Prove2me | Theorems.Thm_Groundwork_SatNet_Consec_succ_unique
-- name    : Groundwork.SatNet.Consec.succ_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:38:47.932846+00:00
-- url     : https://prove2.me/theorems/d8dc5815-419e-4da3-b841-f09f6cbc0928
-- title:
--   Consec: succ unique
-- statement:
--   A slot has at most one successor.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SatNet.lean#L44-L52
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SatNet.lean#L44-L52

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

theorem Groundwork.SatNet.Consec.succ_unique (hidx : Function.Injective idx) {p q q' : ι}
    (h : Consec idx lab p q) (h' : Consec idx lab p q') : q = q' := by sorry
