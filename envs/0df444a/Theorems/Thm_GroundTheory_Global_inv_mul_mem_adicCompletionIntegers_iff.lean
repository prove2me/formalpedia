-- Prove2me | Theorems.Thm_GroundTheory_Global_inv_mul_mem_adicCompletionIntegers_iff
-- name    : GroundTheory.Global.inv_mul_mem_adicCompletionIntegers_iff
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T01:13:51.832315+00:00
-- url     : https://prove2.me/theorems/7c582a4c-ea88-4cec-a6ff-bc2bc62d6aa0
-- title:
--   Global: inv mul mem adic Completion Integers iff
-- statement:
--   The Global construction uses the inv mul mem adic Completion Integers iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/FiniteAdeleScaling.lean#L147-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/FiniteAdeleScaling.lean#L147-L167

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleMeasure
import Definitions.Def_GroundTheory_GlobalFields_LocalFieldAtPlace
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_FiniteAdeleScaling
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain MeasureTheory Measure
open scoped NumberField.AdeleRing ENNReal NNReal Pointwise
noncomputable section
variable {K : Type*} [Field K] [NumberField K]

theorem GroundTheory.Global.inv_mul_mem_adicCompletionIntegers_iff {v : HeightOneSpectrum (𝓞 K)}
    {ϖ : v.adicCompletionIntegers K} (hϖ : Irreducible ϖ) (x : v.adicCompletion K) :
    (ϖ : v.adicCompletion K)⁻¹ * x ∈ v.adicCompletionIntegers K ↔
      ∃ h : x ∈ v.adicCompletionIntegers K, (⟨x, h⟩ : v.adicCompletionIntegers K) ∈
        IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) := by sorry
