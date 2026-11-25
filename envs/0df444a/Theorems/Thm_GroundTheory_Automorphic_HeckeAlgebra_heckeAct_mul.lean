-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HeckeAlgebra_heckeAct_mul
-- name    : GroundTheory.Automorphic.HeckeAlgebra.heckeAct_mul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T01:44:31.717603+00:00
-- url     : https://prove2.me/theorems/45903659-1fba-5812-abf9-2452e2d0b6e1
-- title:
--   Hecke Algebra: hecke Act mul
-- statement:
--   The Hecke Algebra construction uses the hecke Act mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HeckeIrreducible.lean#L26-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HeckeIrreducible.lean#L26-L30

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
omit [μ.IsHaarMeasure]

theorem GroundTheory.Automorphic.HeckeAlgebra.heckeAct_mul [IsFiniteMeasureOnCompacts μ] [μ.IsMulLeftInvariant] (a b : HeckeAlgebra μ)
    {v : V} (hv : v ∈ smoothVectors ρ) :
    heckeAct μ ρ (a * b : HeckeAlgebra μ) v = heckeAct μ ρ a (heckeAct μ ρ b v) := by sorry
