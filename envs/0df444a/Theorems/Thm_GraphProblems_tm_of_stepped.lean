-- Prove2me | Theorems.Thm_GraphProblems_tm_of_stepped
-- name    : GraphProblems.tm_of_stepped
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:55:43.302407+00:00
-- url     : https://prove2.me/theorems/bc5ef5be-f70d-46ee-97b8-63008c13b128
-- title:
--   Graph Problems: tm of stepped
-- statement:
--   The Graph Problems construction uses the tm of stepped property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/GraphProblems/Host.lean#L27-L67
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/GraphProblems/Host.lean#L27-L67

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountKSat_Interfaces
import Definitions.Def_ToTuring_Machine_EndTM
import Definitions.Def_CountKSat_Host
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_GraphProblems_Host
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
open GraphProblems
open Groundwork CountKSat Turing

theorem GraphProblems.tm_of_stepped (M : Stepped (List Bool) (List Bool)) [IsPolyT M] {ι : Type} (code out : ι → List Bool) (sz : ι → ℕ)
    {δ : ℝ} (hδ : 0 < δ) (c a d : ℕ) (hlen : ∀ x, (code x).length + 1 ≤ a * (sz x + 2) ^ d)
    (h : ∀ x, ∃ T : ℕ, M.Runs (code x) T (c * (sz x + 2) ^ c) (out x) ∧ (T : ℝ) ≤ c * (2 : ℝ) ^ (δ / 2 * sz x)) :
    ∃ (N : TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (N.tm.Γ i)) ∧ ∀ x,
      Nonempty (TM2OutputsInTime N.tm ((code x).map N.inputAlphabet.invFun) (some ((out x).map N.outputAlphabet.invFun))
        ⌊(C : ℝ) * (2 : ℝ) ^ (δ * sz x)⌋₊) := by sorry
