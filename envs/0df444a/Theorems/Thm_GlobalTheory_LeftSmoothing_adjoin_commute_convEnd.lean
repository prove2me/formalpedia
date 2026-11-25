-- Prove2me | Theorems.Thm_GlobalTheory_LeftSmoothing_adjoin_commute_convEnd
-- name    : GlobalTheory.LeftSmoothing.adjoin_commute_convEnd
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T01:22:01.580813+00:00
-- url     : https://prove2.me/theorems/63d9b253-d6a5-4fce-a642-719b391c8251
-- title:
--   Left Smoothing: adjoin commute conv End
-- statement:
--   The Left Smoothing construction uses the adjoin commute conv End property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LeftSmoothingProdExpSmoothCommute.lean#L180-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LeftSmoothingProdExpSmoothCommute.lean#L180-L194

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ExpHaar
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraInvariance_Compact
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavin
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_ParametricIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LeftSmoothingProdExpSmoothCommute
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
open GlobalTheory GlobalTheory.LeftSmoothing
open scoped Manifold Topology
open Set Filter
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}
variable (h : IsExpLieAlgebra G 𝔤) {n : ℕ} (X : Fin n → 𝔤) (κ : (Fin n → ℝ) → ℂ)
variable {h X κ}

theorem GlobalTheory.LeftSmoothing.adjoin_commute_convEnd (hκ : Continuous κ) (hκs : HasCompactSupport κ)
    {T : Module.End ℂ (h.smoothFuns (F := ℂ))}
    (hT : T ∈ Algebra.adjoin ℂ (Set.range (h.rightDerivEnd (F := ℂ)))) :
    T * convEnd h X hκ hκs = convEnd h X hκ hκs * T := by sorry
