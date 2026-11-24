-- Prove2me | Theorems.Thm_GlobalTheory_TestLat_Model_valAt_bijective
-- name    : GlobalTheory.TestLat.Model.valAt_bijective
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:15:33.449058+00:00
-- url     : https://prove2.me/theorems/dab178e9-e686-4740-be50-4c52dfccd40a
-- title:
--   Model: val At bijective
-- statement:
--   The Model construction uses the val At bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/NotIsSelfDualETwo.lean#L34-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/NotIsSelfDualETwo.lean#L34-L42

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsSelfDualE
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_NotIsSelfDualETwo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open Formalism.BasicNotions Formalism.L2.DIV
open scoped Matrix ComplexOrder
noncomputable section
open GlobalTheory GlobalTheory.TestLat GlobalTheory.TestLat.Model
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {n N : ℕ} {C : Type}
open NumberField
open scoped Matrix ComplexOrder
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {n N : ℕ} {C : Type}
omit [NumberField K]

theorem GlobalTheory.TestLat.Model.valAt_bijective (lam : ι → _root_.Formalism.BasicNotions.DomWeight n) (e : Fin N ≃ C × _root_.Formalism.L2.DIV.VVIdx lam) :
    Function.Bijective fun (u : Fin N → K) (c : C) => _root_.GlobalTheory.TestLat.valAt lam e c u := by sorry
