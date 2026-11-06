-- Prove2me | Theorems.Thm_MinOfBounds_alternation_outputs
-- name    : MinOfBounds.alternation_outputs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:10:36.326766+00:00
-- url     : https://prove2.me/theorems/d37911e0-589f-4407-91cb-e8ad3ff7ac7e
-- title:
--   Min Of Bounds: alternation outputs
-- statement:
--   The alternation with any last step. Let `pre` rename the variables that occur, let M₁ with C₁
--   meet the bound in m and M₂ with C₂ the bound of Theorem D (b), and let N run M₁ and M₂ in
--   alternation behind `pre`, with the same function `post` after either. Then there is a constant C
--   such that, for every k ≥ 1 and every
--   k-CNF φ with m ≥ 2 clauses in which n ≥ 4 variables occur, N, started on the compact code of (k, φ),
--   puts out `post` of the number of satisfying assignments of φ, as assignments of these n variables,
--   within the bound of Corollary 11 with the constant C.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/MinOfBounds/Main.lean#L81-L95
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/MinOfBounds/Main.lean#L81-L95

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_MinOfBounds_Defs
import Definitions.Def_MinOfBounds_Rename
import Definitions.Def_MinOfBounds_Arith
import Definitions.Def_TwoMachines_Main
import Definitions.Def_Wrap_Sim
import Definitions.Def_ToTuring_Closure_Basic
import Definitions.Def_VariableBound_Paper_Arith
import Definitions.Def_VariableBound_Paper_MainTheorem
import Definitions.Def_VariableBound_Paper_Rename_Compact
import Definitions.Def_VariableBound_Paper_Rename_End
import Definitions.Def_MinOfBounds_Main
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open MinOfBounds
open Turing Groundwork Wrap TwoMachines MainTheoremForms
open Sat3 (CNF)

theorem MinOfBounds.alternation_outputs {pre : List Bool → List Bool} (hpre : RenamesTheVariablesThatOccur pre) {M₁ : TM2ComputableAux Bool Bool} {C₁ : ℕ} (h₁ : MeetsBoundInM M₁ C₁)
    {M₂ : TM2ComputableAux Bool Bool} {C₂ : ℕ} (h₂ : ThmVariablesBFor M₂ C₂) {post : List Bool → List Bool} {N : TM2ComputableAux Bool Bool} {q : ℕ} (hN : Alternates M₁ M₂ pre pre post post N q) :
    ∃ C : ℕ, ∀ (k V : ℕ) (φ : CNF V), 1 ≤ k → SatK.IsKCNF k φ → 2 ≤ φ.length → 4 ≤ numOcc φ →
      Outputs N (encC k φ) (post (SatK.binary (numOcc φ) (numSatOcc φ))) (timeCor C k φ.length (numOcc φ) + C * (encC k φ).length ^ C) := by sorry
