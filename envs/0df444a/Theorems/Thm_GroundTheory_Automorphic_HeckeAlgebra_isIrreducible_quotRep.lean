-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HeckeAlgebra_isIrreducible_quotRep
-- name    : GroundTheory.Automorphic.HeckeAlgebra.isIrreducible_quotRep
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T02:59:09.817272+00:00
-- url     : https://prove2.me/theorems/c99dd002-49ed-44db-87ea-b0f919b0cd35
-- title:
--   Hecke Algebra: is Irreducible quot Rep
-- statement:
--   The Hecke Algebra construction uses the is Irreducible quot Rep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HeckeIrreducible.lean#L286-L344
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HeckeIrreducible.lean#L286-L344

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
variable (I : Submodule (HeckeAlgebraLevel μ K hKc hKo) (HeckeAlgebraLevel μ K hKc hKo))

theorem GroundTheory.Automorphic.HeckeAlgebra.isIrreducible_quotRep (hI : IsCoatom I) : (quotRep hKc hKo I).IsIrreducible := by sorry
