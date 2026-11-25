-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HeckeAlgebra_heckeAct_idem_eq_fixedProj
-- name    : GroundTheory.Automorphic.HeckeAlgebra.heckeAct_idem_eq_fixedProj
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T01:02:03.218701+00:00
-- url     : https://prove2.me/theorems/9bbf73c6-6834-4a5a-9900-7fbd81c033c3
-- title:
--   Hecke Algebra: hecke Act idem eq fixed Proj
-- statement:
--   The Hecke Algebra construction uses the hecke Act idem eq fixed Proj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HeckeAlgebraLevel.lean#L96-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HeckeAlgebraLevel.lean#L96-L108

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

theorem GroundTheory.Automorphic.HeckeAlgebra.heckeAct_idem_eq_fixedProj (hρ : IsSmooth ρ) (v : V) :
    heckeAct μ ρ (idem μ hKc hKo) v = fixedProj ρ hρ hKc hKo v := by sorry
