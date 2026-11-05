-- Prove2me | Theorems.Thm_Groundwork_Grid_card_sideCut_lab
-- name    : Groundwork.Grid.card_sideCut_lab
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:17:38.685437+00:00
-- url     : https://prove2.me/theorems/3fe82b2b-a94f-410d-98e9-a85ee1afa1c6
-- title:
--   Grid: card side Cut lab
-- statement:
--   There are at most 2^cap labels.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/CutWord.lean#L104-L105
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/CutWord.lean#L104-L105

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Math_Sparse
import Definitions.Def_Groundwork_Grid_Expand
import Definitions.Def_StepMachines_Math_CutWord
set_option autoImplicit false
section
section
open Groundwork Groundwork.Grid
open Finset
open Groundwork.Prog (tb capW)

theorem Groundwork.Grid.card_sideCut_lab (tr : Bool) (n i : ℕ) : #(sideCut tr n i).lab ≤ 2 ^ (sideCut tr n i).cap := by sorry
