-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HeckeAlgebra_HeckeAlgebraLevel_coe_smul_fixedVectors
-- name    : GroundTheory.Automorphic.HeckeAlgebra.HeckeAlgebraLevel.coe_smul_fixedVectors
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T01:01:45.225435+00:00
-- url     : https://prove2.me/theorems/a736b9eb-3cb4-4ceb-b59a-2a100e915240
-- title:
--   Hecke Algebra Level: coe smul fixed Vectors
-- statement:
--   The Hecke Algebra Level construction uses the coe smul fixed Vectors property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HeckeAlgebraLevel.lean#L269-L270
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HeckeAlgebraLevel.lean#L269-L270

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
open GroundTheory.Automorphic.HeckeAlgebra.HeckeAlgebraLevel

theorem GroundTheory.Automorphic.HeckeAlgebra.HeckeAlgebraLevel.coe_smul_fixedVectors (h : HeckeAlgebraLevel μ K hKc hKo) (v : fixedVectors ρ K) :
    ((h • v : fixedVectors ρ K) : V) = heckeAct μ ρ (h : HeckeAlgebra μ) v := by sorry
