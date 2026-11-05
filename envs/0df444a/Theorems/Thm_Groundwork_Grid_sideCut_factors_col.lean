-- Prove2me | Theorems.Thm_Groundwork_Grid_sideCut_factors_col
-- name    : Groundwork.Grid.sideCut_factors_col
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:57:21.050589+00:00
-- url     : https://prove2.me/theorems/639ab98b-952b-4491-9340-68fb5115a76d
-- title:
--   Grid: side Cut factors col
-- statement:
--   Across columns the cut is a factorisation of A_i, its arguments in the order x, u | y, v.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/CutWord.lean#L97-L101
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/CutWord.lean#L97-L101

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

theorem Groundwork.Grid.sideCut_factors_col (n i : ℕ) : (sideCut true n i).Factors fun x u y v => A n i x y u v := by sorry
