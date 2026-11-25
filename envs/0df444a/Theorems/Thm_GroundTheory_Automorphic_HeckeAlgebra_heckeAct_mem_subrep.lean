-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HeckeAlgebra_heckeAct_mem_subrep
-- name    : GroundTheory.Automorphic.HeckeAlgebra.heckeAct_mem_subrep
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:13:28.135901+00:00
-- url     : https://prove2.me/theorems/0436f7d4-29e4-456e-afae-5beb1f2cc4e0
-- title:
--   Hecke Algebra: hecke Act mem subrep
-- statement:
--   The Hecke Algebra construction uses the hecke Act mem subrep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HeckeIrreducible.lean#L36-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HeckeIrreducible.lean#L36-L41

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

theorem GroundTheory.Automorphic.HeckeAlgebra.heckeAct_mem_subrep (X : Subrepresentation ρ) {f : G → ℂ}
    (hf : f ∈ locallyConstantCompactSupport G ℂ ℂ) {x : V} (hx : x ∈ smoothVectors ρ)
    (hX : x ∈ X) : heckeAct μ ρ f x ∈ X := by sorry
