-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HeckeAlgebra_heckeAct_corner
-- name    : GroundTheory.Automorphic.HeckeAlgebra.heckeAct_corner
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T01:44:51.806597+00:00
-- url     : https://prove2.me/theorems/d1f5af8e-afb8-49e9-8ba2-df2919b9056f
-- title:
--   Hecke Algebra: hecke Act corner
-- statement:
--   The Hecke Algebra construction uses the hecke Act corner property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HeckeIrreducible.lean#L43-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HeckeIrreducible.lean#L43-L47

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HeckeAlgebraLevel
import Definitions.Def_GroundTheory_AutomorphicForms_HeckeIrreducible
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u
open GroundTheory GroundTheory.Automorphic
open Set Filter Topology MeasureTheory
open scoped Pointwise
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsHaarMeasure]
  {K : Subgroup G} (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G))
open GroundTheory.Automorphic.HeckeAlgebra
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}

theorem GroundTheory.Automorphic.HeckeAlgebra.heckeAct_corner {v : V} (hv : v ∈ fixedVectors ρ K) (f : HeckeAlgebra μ) :
    heckeAct μ ρ (HeckeAlgebraLevel.corner hKc hKo f : HeckeAlgebra μ) v =
      heckeAct μ ρ (idem μ hKc hKo * f : HeckeAlgebra μ) v := by sorry
