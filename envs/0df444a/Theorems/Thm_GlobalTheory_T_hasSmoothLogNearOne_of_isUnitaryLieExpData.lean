-- Prove2me | Theorems.Thm_GlobalTheory_T_hasSmoothLogNearOne_of_isUnitaryLieExpData
-- name    : GlobalTheory.T.hasSmoothLogNearOne_of_isUnitaryLieExpData
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T20:42:31.384247+00:00
-- url     : https://prove2.me/theorems/70a2b035-ac05-4b48-b716-27dbeb7b97ec
-- title:
--   T: has Smooth Log Near One of is Unitary Lie Exp Data
-- statement:
--   The T construction uses the has Smooth Log Near One of is Unitary Lie Exp Data property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/HasSmoothLogNearOneOfIsUnitaryLieExpDataStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/HasSmoothLogNearOneOfIsUnitaryLieExpDataStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_HasSmoothLogNearOneOfIsUnitaryLieExpData
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_HasSmoothLogNearOneOfIsUnitaryLieExpDataStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.hasSmoothLogNearOne_of_isUnitaryLieExpData : ∀ (𝔸 L G : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] [NormedAddCommGroup L] [NormedSpace ℝ L] [Group G] (σ : 𝔸 →ₗ[ℝ] 𝔸) (j : L →ₗ[ℝ] 𝔸) (s : 𝔸 → G), IsLieData σ j s → HasLog σ j := by sorry
