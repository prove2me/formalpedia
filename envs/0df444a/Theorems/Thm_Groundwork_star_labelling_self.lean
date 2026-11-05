-- Prove2me | Theorems.Thm_Groundwork_star_labelling_self
-- name    : Groundwork.star_labelling_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:41:42.231084+00:00
-- url     : https://prove2.me/theorems/d39fb505-251c-4bee-9e58-307da38cb910
-- title:
--   Groundwork: star labelling self
-- statement:
--   The Groundwork construction uses the star labelling self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Brute.lean#L36-L40
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Brute.lean#L36-L40

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

theorem Groundwork.star_labelling_self (K ℓ : ℕ) (d w : List Bool) (v : Fin K) :
    star (labelling K ℓ d w) v v = d := by sorry
