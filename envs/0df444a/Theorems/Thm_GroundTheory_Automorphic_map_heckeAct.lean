-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_map_heckeAct
-- name    : GroundTheory.Automorphic.map_heckeAct
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T01:08:28.351895+00:00
-- url     : https://prove2.me/theorems/904baf41-e6ed-49f1-8fe1-efaf4589805d
-- title:
--   Automorphic: map hecke Act
-- statement:
--   The Automorphic construction uses the map hecke Act property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HeckeAlgebra.lean#L265-L275
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HeckeAlgebra.lean#L265-L275

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HaarCosets
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Definitions.Def_GroundTheory_AutomorphicForms_HeckeAlgebra
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
open Set Filter Topology MeasureTheory
open scoped Pointwise ENNReal
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]
variable (μ : Measure G) {V : Type*} [AddCommGroup V] [Module ℂ V]
variable {μ} {ρ : Representation ℂ G V}
variable [IsFiniteMeasureOnCompacts μ]

theorem GroundTheory.Automorphic.map_heckeAct {W : Type*} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ G W}
    (T : Representation.IntertwiningMap ρ σ) {f : G → ℂ}
    (hf : f ∈ locallyConstantCompactSupport G ℂ ℂ) {v : V} (hv : v ∈ smoothVectors ρ) :
    T (heckeAct μ ρ f v) = heckeAct μ σ f (T v) := by sorry
