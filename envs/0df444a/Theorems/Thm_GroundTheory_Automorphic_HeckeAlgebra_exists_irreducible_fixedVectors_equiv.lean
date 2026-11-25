-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HeckeAlgebra_exists_irreducible_fixedVectors_equiv
-- name    : GroundTheory.Automorphic.HeckeAlgebra.exists_irreducible_fixedVectors_equiv
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T02:58:02.479853+00:00
-- url     : https://prove2.me/theorems/80265075-4ed6-54e5-8ebf-1c3affed4d53
-- title:
--   Hecke Algebra: exists irreducible fixed Vectors equiv
-- statement:
--   The Hecke Algebra construction uses the exists irreducible fixed Vectors equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HeckeIrreducible.lean#L423-L437
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HeckeIrreducible.lean#L423-L437

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

theorem GroundTheory.Automorphic.HeckeAlgebra.exists_irreducible_fixedVectors_equiv (M : Type*) [AddCommGroup M]
    [Module (HeckeAlgebraLevel μ K hKc hKo) M] [IsSimpleModule (HeckeAlgebraLevel μ K hKc hKo) M] :
    ∃ (V : Type u) (_ : AddCommGroup V) (_ : Module ℂ V) (ρ : Representation ℂ G V),
      IsSmooth ρ ∧ ρ.IsIrreducible ∧
        Nonempty (fixedVectors ρ K ≃ₗ[HeckeAlgebraLevel μ K hKc hKo] M) := by sorry
