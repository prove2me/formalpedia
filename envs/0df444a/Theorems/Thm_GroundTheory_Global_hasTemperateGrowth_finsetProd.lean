-- Prove2me | Theorems.Thm_GroundTheory_Global_hasTemperateGrowth_finsetProd
-- name    : GroundTheory.Global.hasTemperateGrowth_finsetProd
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:43:24.056456+00:00
-- url     : https://prove2.me/theorems/ac860f60-0152-4e25-be2a-0d03a5eda0a6
-- title:
--   Global: has Temperate Growth finset Prod
-- statement:
--   The Global construction uses the has Temperate Growth finset Prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/EulerFactorsInfinite.lean#L16-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/EulerFactorsInfinite.lean#L16-L25

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_EulerFactorsArch
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianSchwartz
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceFourier
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_HeckeCharRayClass
import Definitions.Def_GroundTheory_GlobalFields_Adele_IntegersLattice
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_EulerFactorsInfinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open NumberField InfinitePlace InfinitePlace.Completion MeasureTheory Complex ComplexConjugate
  NumberField.mixedEmbedding Function
open scoped Real SchwartzMap Classical RealInnerProductSpace
open GroundTheory GroundTheory.Global
noncomputable section

theorem GroundTheory.Global.hasTemperateGrowth_finsetProd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} (s : Finset ι) {f : ι → E → ℂ} (hf : ∀ i ∈ s, (f i).HasTemperateGrowth) :
    (fun x ↦ ∏ i ∈ s, f i x).HasTemperateGrowth := by sorry
