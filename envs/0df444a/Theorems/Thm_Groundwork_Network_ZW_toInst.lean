-- Prove2me | Theorems.Thm_Groundwork_Network_ZW_toInst
-- name    : Groundwork.Network.ZW_toInst
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:14:46.998687+00:00
-- url     : https://prove2.me/theorems/52d19c49-a954-42f5-bd5a-3b0e3a2df0b6
-- title:
--   Network: ZW to Inst
-- statement:
--   The instance N.toInst D dec has the value of the network N. Its labels are words: x ∈ D a b ⊆
--   words ℓ stands for the
--   label dec a b x of N, and x ↦ dec a b x carries sums over D a b to sums over the labels of N.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/NetVal.lean#L24-L57
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/NetVal.lean#L24-L57

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_NetProg
import Definitions.Def_StepMachines_Prog_NetVal
set_option autoImplicit false
section
open Groundwork
open Finset

theorem Groundwork.Network.ZW_toInst {J σ τ : Type*} [Fintype J] [LinearOrder J] (N : Network J σ τ) (ℓ : ℕ) (d : List Bool)
    (D : J → J → Finset (List Bool)) (dec : J → J → List Bool → τ) (hD : ∀ a b, a < b → D a b ⊆ words ℓ)
    (h : ∀ a b, a < b → ∀ F : τ → ℤ, ∑ x ∈ D a b, F (dec a b x) = ∑ θ ∈ N.Θ a b, F θ) :
    Inst.ZW ℓ d (N.toInst D dec) = N.value := by sorry
