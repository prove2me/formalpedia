-- Prove2me | Theorems.Thm_Groundwork_Host_outputs_of_within
-- name    : Groundwork.Host.outputs_of_within
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:50:46.661596+00:00
-- url     : https://prove2.me/theorems/07d658ef-a0a6-4de9-a1a6-54ea737cacaf
-- title:
--   Host: outputs of within
-- statement:
--   A run of the fragment is a run of the bundled machine, in Mathlib's terms.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Machine/Host.lean#L287-L295
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Machine/Host.lean#L287-L295

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Machine_Lift
import Definitions.Def_ToTuring_PolyT
import Definitions.Def_ToTuring_EncLemmas
import Definitions.Def_ToTuring_Machine_Host
set_option autoImplicit false
section
section
open Groundwork
open TM Turing
open Groundwork.Host

theorem Groundwork.Host.outputs_of_within {H : FrIO} {x y : List Bool} {t : ℕ}
    (h : Frag.Within H (withIO x (st [] [] [] [])) t (withIO y (st [] [] [] []))) {x' y' : List Bool} (hx : x' = x)
    (hy : y' = y) : Nonempty (TM2OutputsInTime (tmOf H) x' (some y') t) := by sorry
