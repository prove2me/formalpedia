-- Prove2me | Theorems.Thm_GlobalTheory_SmoothForms_anti_map_exp
-- name    : GlobalTheory.SmoothForms.anti_map_exp
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T20:19:32.178898+00:00
-- url     : https://prove2.me/theorems/451a6c3a-be96-4b04-b81d-d144fc02bab3
-- title:
--   Smooth Forms: anti map exp
-- statement:
--   The Smooth Forms construction uses the anti map exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/HasSmoothLogNearOneOfIsUnitaryLieExpData.lean#L9-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/HasSmoothLogNearOneOfIsUnitaryLieExpData.lean#L9-L22

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

theorem GlobalTheory.SmoothForms.anti_map_exp {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] (σ : 𝔸 →ₗ[ℝ] 𝔸)
    (anti : ∀ a b, σ (a * b) = σ b * σ a) (one : σ 1 = 1) (X : 𝔸) :
    σ (NormedSpace.exp X) = NormedSpace.exp (σ X) := by sorry
