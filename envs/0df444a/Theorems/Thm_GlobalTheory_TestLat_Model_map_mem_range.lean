-- Prove2me | Theorems.Thm_GlobalTheory_TestLat_Model_map_mem_range
-- name    : GlobalTheory.TestLat.Model.map_mem_range
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:14:57.868802+00:00
-- url     : https://prove2.me/theorems/e15fbd20-a22a-44ac-8dc8-328cb3ab3a7c
-- title:
--   Model: map mem range
-- statement:
--   The Model construction uses the map mem range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/NotIsSelfDualETwo.lean#L124-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/NotIsSelfDualETwo.lean#L124-L127

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsSelfDualE
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_NotIsSelfDualETwo
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap

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

theorem GlobalTheory.TestLat.Model.map_mem_range (σ : K →+* K) {x : K} (hx : x ∈ (algebraMap (𝓞 K) K).range) :
    σ x ∈ (algebraMap (𝓞 K) K).range := by sorry
