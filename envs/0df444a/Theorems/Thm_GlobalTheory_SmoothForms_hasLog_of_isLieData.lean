-- Prove2me | Theorems.Thm_GlobalTheory_SmoothForms_hasLog_of_isLieData
-- name    : GlobalTheory.SmoothForms.hasLog_of_isLieData
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:29:20.155806+00:00
-- url     : https://prove2.me/theorems/12f717a1-6fe8-461b-866b-b9a859e5096e
-- title:
--   Smooth Forms: has Log of is Lie Data
-- statement:
--   The Smooth Forms construction uses the has Log of is Lie Data property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/HasSmoothLogNearOneOfIsUnitaryLieExpData.lean#L39-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/HasSmoothLogNearOneOfIsUnitaryLieExpData.lean#L39-L68

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_HasSmoothLogNearOneOfIsUnitaryLieExpData
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology
open GlobalTheory GlobalTheory.SmoothForms

theorem GlobalTheory.SmoothForms.hasLog_of_isLieData (𝔸 L G : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸]
    [NormedAddCommGroup L] [NormedSpace ℝ L] [Group G] (σ : 𝔸 →ₗ[ℝ] 𝔸) (j : L →ₗ[ℝ] 𝔸) (s : 𝔸 → G)
    (H : IsLieData σ j s) : HasLog σ j := by sorry
