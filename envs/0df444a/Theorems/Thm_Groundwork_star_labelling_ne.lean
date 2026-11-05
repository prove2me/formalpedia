-- Prove2me | Theorems.Thm_Groundwork_star_labelling_ne
-- name    : Groundwork.star_labelling_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:41:44.561782+00:00
-- url     : https://prove2.me/theorems/ac1da599-6163-42a3-bb27-e60a6068738b
-- title:
--   Groundwork: star labelling ne
-- statement:
--   The Groundwork construction uses the star labelling ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Brute.lean#L42-L49
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Brute.lean#L42-L49

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Range
import Definitions.Def_StepMachines_Prog_Chunks
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.OfFn
import Definitions.Def_StepMachines_Prog_Brute
set_option autoImplicit false
section
open Groundwork
open Finset Stepped

theorem Groundwork.star_labelling_ne (K ℓ : ℕ) (d w : List Bool) {v u : Fin K} (h : u ≠ v) :
    star (labelling K ℓ d w) v u = block ℓ (tri (min v.1 u.1) (max v.1 u.1)) w := by sorry
