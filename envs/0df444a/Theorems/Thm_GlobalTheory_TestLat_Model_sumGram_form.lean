-- Prove2me | Theorems.Thm_GlobalTheory_TestLat_Model_sumGram_form
-- name    : GlobalTheory.TestLat.Model.sumGram_form
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:14:15.77832+00:00
-- url     : https://prove2.me/theorems/39032494-6910-458e-8bc8-9702526117f8
-- title:
--   Model: sum Gram form
-- statement:
--   The Model construction uses the sum Gram form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/NotIsSelfDualETwo.lean#L49-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/NotIsSelfDualETwo.lean#L49-L70

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

theorem GlobalTheory.TestLat.Model.sumGram_form [StarRing K] [Fintype C] (lam : ι → _root_.Formalism.BasicNotions.DomWeight n)
    (e : Fin N ≃ C × _root_.Formalism.L2.DIV.VVIdx lam)
    (G : ι → Matrix (Fin n) (Fin n) K) (u w : Fin N → K) :
    star u ⬝ᵥ (_root_.GlobalTheory.TestLat.sumGram lam e G *ᵥ w) =
      ∑ c, _root_.Formalism.L2.DIV.pairK lam G (_root_.GlobalTheory.TestLat.valAt lam e c u)
        (_root_.GlobalTheory.TestLat.valAt lam e c w) := by sorry
