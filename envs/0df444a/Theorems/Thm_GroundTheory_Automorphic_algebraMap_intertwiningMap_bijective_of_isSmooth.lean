-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_algebraMap_intertwiningMap_bijective_of_isSmooth
-- name    : GroundTheory.Automorphic.algebraMap_intertwiningMap_bijective_of_isSmooth
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:13:44.191392+00:00
-- url     : https://prove2.me/theorems/070a4cc7-0c77-4962-9ae1-7372b85bf5cf
-- title:
--   Automorphic: algebra Map intertwining Map bijective of is Smooth
-- statement:
--   The Automorphic construction uses the algebra Map intertwining Map bijective of is Smooth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SmoothRepSchur.lean#L179-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SmoothRepSchur.lean#L179-L181

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepSchur
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
open Polynomial Cardinal
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace.SeparableSpace G] {V : Type*} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ G V}

theorem GroundTheory.Automorphic.algebraMap_intertwiningMap_bijective_of_isSmooth (hρ : IsSmooth ρ) [ρ.IsIrreducible] :
    Function.Bijective (algebraMap ℂ (Representation.IntertwiningMap ρ ρ)) := by sorry
