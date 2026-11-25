-- Prove2me | Theorems.Thm_GlobalTheory_ConvSmooth_conv_smooth_compactSupport
-- name    : GlobalTheory.ConvSmooth.conv_smooth_compactSupport
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T02:38:21.539159+00:00
-- url     : https://prove2.me/theorems/a7271f8f-d3e4-510a-a4b4-3d50a7d50146
-- title:
--   Conv Smooth: conv smooth compact Support
-- statement:
--   The Conv Smooth construction uses the conv smooth compact Support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ConvSmoothCompactSupport.lean#L53-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ConvSmoothCompactSupport.lean#L53-L127

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ExpHaar
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraInvariance_Compact
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavin
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_ParametricIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LintegralInvLeOfSupportCompactStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSmoothFunIntegralMulRightStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ConvSmoothCompactSupport
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GroundTheory.Automorphic
open scoped ContDiff
open GlobalTheory GlobalTheory.ConvSmooth

theorem GlobalTheory.ConvSmooth.conv_smooth_compactSupport : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) [MeasurableSpace G] [BorelSpace G] (μ : Measure G), μ.IsHaarMeasure → ∀ K : Set G, IsCompact K → ∀ κ a : G → ℂ, h.IsSmoothFun κ → HasCompactSupport κ → Measurable a → Integrable a μ → (∀ x ∉ K, a x = 0) → h.IsSmoothFun (fun z => ∫ x, κ x * a (x⁻¹ * z) ∂μ) ∧ HasCompactSupport (fun z => ∫ x, κ x * a (x⁻¹ * z) ∂μ) := by sorry
