-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HeckeAlgebra_nonempty_equiv_quotRep
-- name    : GroundTheory.Automorphic.HeckeAlgebra.nonempty_equiv_quotRep
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T01:46:42.892165+00:00
-- url     : https://prove2.me/theorems/542a9e5f-dcd1-4399-bbd9-953a5b45654a
-- title:
--   Hecke Algebra: nonempty equiv quot Rep
-- statement:
--   The Hecke Algebra construction uses the nonempty equiv quot Rep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HeckeIrreducible.lean#L363-L421
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HeckeIrreducible.lean#L363-L421

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
open HeckeAlgebraLevel
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}

theorem GroundTheory.Automorphic.HeckeAlgebra.nonempty_equiv_quotRep (I : Submodule (HeckeAlgebraLevel μ K hKc hKo)
    (HeckeAlgebraLevel μ K hKc hKo)) (hρ : IsSmooth ρ) [ρ.IsIrreducible] {v₀ : V}
    (hv₀ : v₀ ∈ fixedVectors ρ K) (h0 : v₀ ≠ 0)
    (hI : ∀ h : HeckeAlgebraLevel μ K hKc hKo, h ∈ I ↔ heckeAct μ ρ (h : HeckeAlgebra μ) v₀ = 0) :
    Nonempty ((quotRep hKc hKo I).Equiv ρ) := by sorry
