-- Prove2me | Theorems.Thm_Groundwork_SatNet_idx_lt_of_fst_lt
-- name    : Groundwork.SatNet.idx_lt_of_fst_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:21:24.902697+00:00
-- url     : https://prove2.me/theorems/4ae6ca0a-e614-42e9-8647-bc61fd39a91e
-- title:
--   Sat Net: idx lt of fst lt
-- statement:
--   The Sat Net construction uses the idx lt of fst lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SatNet.lean#L252-L263
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SatNet.lean#L252-L263

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
variable {V : Type}
variable [DecidableEq V]
variable {φ : List (List (V × Bool))} {g μ k : ℕ}

theorem Groundwork.SatNet.idx_lt_of_fst_lt {p q : Slot g μ k} (h : p.1 < q.1) : idx p < idx q := by sorry
