-- Prove2me | Theorems.Thm_GlobalTheory_LeftSmoothing_rightDeriv_conv
-- name    : GlobalTheory.LeftSmoothing.rightDeriv_conv
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T01:16:16.425156+00:00
-- url     : https://prove2.me/theorems/85e4cfc7-f0c5-482a-8692-0722eb73be84
-- title:
--   Left Smoothing: right Deriv conv
-- statement:
--   The Left Smoothing construction uses the right Deriv conv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LeftSmoothingProdExpSmoothCommute.lean#L126-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LeftSmoothingProdExpSmoothCommute.lean#L126-L148

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

theorem GlobalTheory.LeftSmoothing.rightDeriv_conv (hκ : Continuous κ) (hκs : HasCompactSupport κ) {f : G → ℂ}
    (hf : h.IsSmoothFun f) (Z : 𝔤) (g : G) :
    h.rightDeriv Z (conv h X κ f) g = conv h X κ (h.rightDeriv Z f) g := by sorry
