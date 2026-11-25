-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HeckeAlgebra_isSmooth_quotRep
-- name    : GroundTheory.Automorphic.HeckeAlgebra.isSmooth_quotRep
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T01:46:29.116915+00:00
-- url     : https://prove2.me/theorems/250507a3-e247-471e-b00e-f4f5c120d223
-- title:
--   Hecke Algebra: is Smooth quot Rep
-- statement:
--   The Hecke Algebra construction uses the is Smooth quot Rep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HeckeIrreducible.lean#L212-L217
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HeckeIrreducible.lean#L212-L217

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

theorem GroundTheory.Automorphic.HeckeAlgebra.isSmooth_quotRep : IsSmooth (quotRep hKc hKo I) := by sorry
