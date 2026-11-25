-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HeckeAlgebra_isSimpleModule_fixedVectors
-- name    : GroundTheory.Automorphic.HeckeAlgebra.isSimpleModule_fixedVectors
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T01:44:46.074663+00:00
-- url     : https://prove2.me/theorems/4420c770-598b-419b-842e-370477e7ad82
-- title:
--   Hecke Algebra: is Simple Module fixed Vectors
-- statement:
--   The Hecke Algebra construction uses the is Simple Module fixed Vectors property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HeckeIrreducible.lean#L86-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HeckeIrreducible.lean#L86-L111

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

theorem GroundTheory.Automorphic.HeckeAlgebra.isSimpleModule_fixedVectors (hρ : IsSmooth ρ) [ρ.IsIrreducible]
    (hK : fixedVectors ρ K ≠ ⊥) :
    IsSimpleModule (HeckeAlgebraLevel μ K hKc hKo) (fixedVectors ρ K) := by sorry
