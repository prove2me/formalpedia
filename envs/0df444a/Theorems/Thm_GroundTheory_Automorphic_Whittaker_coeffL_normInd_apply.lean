-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_coeffL_normInd_apply
-- name    : GroundTheory.Automorphic.Whittaker.coeffL_normInd_apply
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T01:02:17.508634+00:00
-- url     : https://prove2.me/theorems/4dca5d4f-a894-4c76-b97b-a1f0b6127d59
-- title:
--   Whittaker: coeff L norm Ind apply
-- statement:
--   The Whittaker construction uses the coeff L norm Ind apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCriterion.lean#L231-L236
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCriterion.lean#L231-L236

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
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
variable (hρ : IsSmooth ρ)
include hρ

theorem GroundTheory.Automorphic.Whittaker.coeffL_normInd_apply [μ.IsMulRightInvariant] (ℓ : Module.Dual ℂ V) {K : Subgroup G} (hKc : IsCompact (K : Set G))
    (hKo : IsOpen (K : Set G)) {v : V} (hv : v ∈ fixedVectors ρ K) :
    ((coeffL μ hρ ℓ ⟨normInd μ K, normInd_mem μ hKc hKo⟩ : smoothVectors (Representation.dual ρ)) :
      Module.Dual ℂ V) v = ℓ v := by sorry
