-- Prove2me | Theorems.Thm_GroundTheory_Global_mem_finiteSingleUnits_smul_iff
-- name    : GroundTheory.Global.mem_finiteSingleUnits_smul_iff
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T01:18:51.225286+00:00
-- url     : https://prove2.me/theorems/b17de40d-7d3d-4cf7-b2cf-4f86f609dba4
-- title:
--   Global: mem finite Single Units smul iff
-- statement:
--   The Global construction uses the mem finite Single Units smul iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/FiniteAdeleScaling.lean#L169-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/FiniteAdeleScaling.lean#L169-L192

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

theorem GroundTheory.Global.mem_finiteSingleUnits_smul_iff (v : HeightOneSpectrum (𝓞 K)) (z : (v.adicCompletion K)ˣ)
    (y : 𝔸ᶠ[K]) :
    y ∈ finiteSingleUnits v z • (integralFiniteAdeles (𝓞 K) K : Set 𝔸ᶠ[K]) ↔
      (∀ w ≠ v, y w ∈ w.adicCompletionIntegers K) ∧
        (z : v.adicCompletion K)⁻¹ * y v ∈ v.adicCompletionIntegers K := by sorry
