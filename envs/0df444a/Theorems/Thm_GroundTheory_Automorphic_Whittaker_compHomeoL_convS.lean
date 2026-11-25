-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_compHomeoL_convS
-- name    : GroundTheory.Automorphic.Whittaker.compHomeoL_convS
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T01:05:25.051933+00:00
-- url     : https://prove2.me/theorems/078b53e2-e788-4226-983d-26056db5ed24
-- title:
--   Whittaker: comp Homeo L conv S
-- statement:
--   The Whittaker construction uses the comp Homeo L conv S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCriterion.lean#L271-L295
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCriterion.lean#L271-L295

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HeckeAlgebra
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepContragredient
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepSchur
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCriterion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Whittaker
open Set Filter Topology MeasureTheory
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [TotallyDisconnectedSpace G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure]
omit [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] [μ.IsHaarMeasure]

theorem GroundTheory.Automorphic.Whittaker.compHomeoL_convS [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    [μ.IsMulLeftInvariant] [μ.IsInvInvariant] (σ : G ≃ₜ G)
    (hσ : ∀ x y, σ (x * y) = σ y * σ x) (hσμ : μ.map σ = μ)
    (f₁ f₂ : locallyConstantCompactSupport G ℂ ℂ) :
    compHomeoL σ (convS μ f₁ f₂) = convS μ (compHomeoL σ f₂) (compHomeoL σ f₁) := by sorry
