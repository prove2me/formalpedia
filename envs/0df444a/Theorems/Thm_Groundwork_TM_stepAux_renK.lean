-- Prove2me | Theorems.Thm_Groundwork_TM_stepAux_renK
-- name    : Groundwork.TM.stepAux_renK
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:11:35.499224+00:00
-- url     : https://prove2.me/theorems/9082708f-f383-46a4-9296-50d309b06d0b
-- title:
--   TM: step Aux ren K
-- statement:
--   One statement: on stacks that agree along φ, the renamed statement ends at the same label with
--   the same local state, on
--   stacks that agree along φ, and it leaves the stacks outside the image of φ alone.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Rename.lean#L50-L74
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Rename.lean#L50-L74

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_TM_Frag
import Definitions.Def_ToTuring_TM_Rename
set_option autoImplicit false
section
section
open Groundwork Groundwork.TM
open Turing
variable {K₁ K₂ : Type} [DecidableEq K₁] [DecidableEq K₂] {A Λ σ : Type} (φ : K₁ → K₂)
variable {φ}

theorem Groundwork.TM.stepAux_renK (hφ : Function.Injective φ) (q : TM2.Stmt (fun _ : K₁ => A) Λ σ) (v : σ) (T : K₁ → List A)
    (S : K₂ → List A) (hS : ∀ k, S (φ k) = T k) :
    (TM2.stepAux (renK φ q) v S).l = (TM2.stepAux q v T).l ∧ (TM2.stepAux (renK φ q) v S).var = (TM2.stepAux q v T).var ∧
      (∀ k, (TM2.stepAux (renK φ q) v S).stk (φ k) = (TM2.stepAux q v T).stk k) ∧
      ∀ k, (∀ a, φ a ≠ k) → (TM2.stepAux (renK φ q) v S).stk k = S k := by sorry
