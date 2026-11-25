-- Prove2me | Theorems.Thm_GlobalTheory_ConvSmooth_isSmoothFun_density
-- name    : GlobalTheory.ConvSmooth.isSmoothFun_density
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T02:38:48.913397+00:00
-- url     : https://prove2.me/theorems/672264bd-095a-49e2-9fdf-8e8bc833e031
-- title:
--   Conv Smooth: is Smooth Fun density
-- statement:
--   The Conv Smooth construction uses the is Smooth Fun density property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ConvSmoothCompactSupport.lean#L19-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ConvSmoothCompactSupport.lean#L19-L41

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

theorem GlobalTheory.ConvSmooth.isSmoothFun_density {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
    [FiniteDimensional ℝ 𝔸] {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (h : IsExpLieAlgebra G 𝔤)
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) {L : Set G} (hL : IsCompact L)
    {κ : G → ℂ} (hκ : h.IsSmoothFun κ) {p : G → NNReal} (hp : Measurable p)
    (hpi : Integrable (fun y => (p y : ℝ)) μ) (hpL : ∀ y ∉ L, p y = 0) :
    h.IsSmoothFun (fun z => ∫ y, κ (z * y) * ((p y : ℝ) : ℂ) ∂μ) := by sorry
