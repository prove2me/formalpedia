-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HeckeAlgebra_nonempty_equiv_of_fixedVectors_equiv
-- name    : GroundTheory.Automorphic.HeckeAlgebra.nonempty_equiv_of_fixedVectors_equiv
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T01:46:38.651672+00:00
-- url     : https://prove2.me/theorems/6666cd0a-a401-4f2b-9777-a015faac2a42
-- title:
--   Hecke Algebra: nonempty equiv of fixed Vectors equiv
-- statement:
--   The Hecke Algebra construction uses the nonempty equiv of fixed Vectors equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HeckeIrreducible.lean#L439-L462
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HeckeIrreducible.lean#L439-L462

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

theorem GroundTheory.Automorphic.HeckeAlgebra.nonempty_equiv_of_fixedVectors_equiv {W : Type*} [AddCommGroup W] [Module ℂ W]
    {σ : Representation ℂ G W} (hρ : IsSmooth ρ) (hσ : IsSmooth σ) [ρ.IsIrreducible]
    [σ.IsIrreducible] (hK : fixedVectors ρ K ≠ ⊥)
    (e : fixedVectors ρ K ≃ₗ[HeckeAlgebraLevel μ K hKc hKo] fixedVectors σ K) :
    Nonempty (ρ.Equiv σ) := by sorry
