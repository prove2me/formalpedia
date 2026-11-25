-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HeckeAlgebra_heckeRep_apply
-- name    : GroundTheory.Automorphic.HeckeAlgebra.heckeRep_apply
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T01:05:25.489826+00:00
-- url     : https://prove2.me/theorems/f26ed985-0e10-49b6-8f4a-3b31cb9d50b6
-- title:
--   Hecke Algebra: hecke Rep apply
-- statement:
--   The Hecke Algebra construction uses the hecke Rep apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HeckeAlgebraLevel.lean#L284-L285
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HeckeAlgebraLevel.lean#L284-L285

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HeckeAlgebra
import Definitions.Def_GroundTheory_AutomorphicForms_HeckeAlgebraLevel
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
  [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  [MeasurableSpace G] [BorelSpace G]
open GroundTheory.Automorphic.HeckeAlgebra
variable (μ : Measure G) [μ.IsHaarMeasure] {K : Subgroup G} (hKc : IsCompact (K : Set G))
  (hKo : IsOpen (K : Set G))
variable {μ}
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}

theorem GroundTheory.Automorphic.HeckeAlgebra.heckeRep_apply (hρ : IsSmooth ρ) (f : HeckeAlgebra μ) (v : V) :
    heckeRep hρ f v = heckeAct μ ρ f v := by sorry
