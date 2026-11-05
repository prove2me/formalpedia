-- Prove2me | Theorems.Thm_Groundwork_card_eq_add_card_ne
-- name    : Groundwork.card_eq_add_card_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:15:55.986196+00:00
-- url     : https://prove2.me/theorems/239fd518-710c-4e88-b444-81b7bc0815bf
-- title:
--   Groundwork: card eq add card ne
-- statement:
--   Every position holds s₀ or another state.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/Sparse.lean#L240-L241
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/Sparse.lean#L240-L241

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_GridDefs
import Definitions.Def_StepMachines_Math_CodeMore
import Definitions.Def_StepMachines_Math_Sparse
set_option autoImplicit false
section
section
open Groundwork
open Finset
open Groundwork.Prog (tb capW)

theorem Groundwork.card_eq_add_card_ne {n : ℕ} (s₀ : Bell) (β : Fin n → Bell) : #{k | β k = s₀} + #{k | β k ≠ s₀} = n := by sorry
