-- Prove2me | Theorems.Thm_Groundwork_query0_eq
-- name    : Groundwork.query0_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:42:00.420021+00:00
-- url     : https://prove2.me/theorems/077c1341-fc88-4c79-8d86-a1e659d0ff47
-- title:
--   Groundwork: query0 eq
-- statement:
--   The Groundwork construction uses the query0 eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Brute.lean#L51-L62
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Brute.lean#L51-L62

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

theorem Groundwork.query0_eq (K ℓ : ℕ) (d w : List Bool) (v : Fin K) :
    query0 K ℓ d w v = (v.1, List.ofFn (star (labelling K ℓ d w) v)) := by sorry
