-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_heckeAct_mem_of_forall
-- name    : GroundTheory.Automorphic.heckeAct_mem_of_forall
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T01:08:33.908022+00:00
-- url     : https://prove2.me/theorems/ab235ee0-7654-491a-9034-23bd453e61dd
-- title:
--   Automorphic: hecke Act mem of forall
-- statement:
--   The Automorphic construction uses the hecke Act mem of forall property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HeckeAlgebra.lean#L175-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HeckeAlgebra.lean#L175-L180

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HaarCosets
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Definitions.Def_GroundTheory_AutomorphicForms_HeckeAlgebra
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
  [MeasurableSpace G] [BorelSpace G]
variable (μ : Measure G) {V : Type*} [AddCommGroup V] [Module ℂ V]
variable {μ} {ρ : Representation ℂ G V}
omit [IsTopologicalGroup G] [BorelSpace G]

theorem GroundTheory.Automorphic.heckeAct_mem_of_forall {f : G → ℂ} {v : V} (hfin : (range fun g => f g • ρ g v).Finite)
    {X : Submodule ℂ V} (hX : ∀ g, f g • ρ g v ∈ X) : heckeAct μ ρ f v ∈ X := by sorry
