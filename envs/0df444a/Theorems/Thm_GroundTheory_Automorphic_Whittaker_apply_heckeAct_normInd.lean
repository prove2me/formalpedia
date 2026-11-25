-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_apply_heckeAct_normInd
-- name    : GroundTheory.Automorphic.Whittaker.apply_heckeAct_normInd
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T01:04:32.588361+00:00
-- url     : https://prove2.me/theorems/4151e896-f1f2-4500-831e-a974ab77d1df
-- title:
--   Whittaker: apply hecke Act norm Ind
-- statement:
--   The Whittaker construction uses the apply hecke Act norm Ind property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCriterion.lean#L534-L552
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCriterion.lean#L534-L552

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
  (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
omit [LocallyCompactSpace G] [TotallyDisconnectedSpace G] [μ.IsMulRightInvariant]

theorem GroundTheory.Automorphic.Whittaker.apply_heckeAct_normInd (hρ : IsSmooth ρ) {K : Subgroup G} (hKc : IsCompact (K : Set G))
    (hKo : IsOpen (K : Set G)) {ξ : smoothVectors (Representation.dual ρ)}
    (hξ : ξ ∈ fixedVectors (contragredient ρ) K) (v : V) :
    (ξ : Module.Dual ℂ V) (heckeAct μ ρ (normInd μ K) v) = (ξ : Module.Dual ℂ V) v := by sorry
