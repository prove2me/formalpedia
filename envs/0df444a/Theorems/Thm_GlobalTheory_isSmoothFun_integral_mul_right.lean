-- Prove2me | Theorems.Thm_GlobalTheory_isSmoothFun_integral_mul_right
-- name    : GlobalTheory.isSmoothFun_integral_mul_right
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T01:13:43.965351+00:00
-- url     : https://prove2.me/theorems/99cb5c62-abd1-4422-98a6-f80f6df4f9b8
-- title:
--   Global Theory: is Smooth Fun integral mul right
-- statement:
--   The Global Theory construction uses the is Smooth Fun integral mul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsSmoothFunIntegralMulRight.lean#L12-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsSmoothFunIntegralMulRight.lean#L12-L55

import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ExpHaar
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraInvariance_Compact
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavin
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_ParametricIntegral
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Garding
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSmoothFunIntegralMulRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GroundTheory.Automorphic
open scoped ContDiff Manifold
open GlobalTheory

theorem GlobalTheory.isSmoothFun_integral_mul_right : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) [MeasurableSpace G] [BorelSpace G] (ν : Measure G) [IsFiniteMeasure ν] (K : Set G), IsCompact K → ν Kᶜ = 0 → ∀ κ : G → ℂ, h.IsSmoothFun κ → h.IsSmoothFun (fun z => ∫ y, κ (z * y) ∂ν) := by sorry
