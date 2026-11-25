-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_algebraMap_intertwiningMap_bijective_of_rank_le_aleph0
-- name    : GroundTheory.Automorphic.algebraMap_intertwiningMap_bijective_of_rank_le_aleph0
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:35:18.494731+00:00
-- url     : https://prove2.me/theorems/76710db3-347b-4c80-a7d6-46f7167736ff
-- title:
--   Automorphic: algebra Map intertwining Map bijective of rank le aleph0
-- statement:
--   The Automorphic construction uses the algebra Map intertwining Map bijective of rank le aleph0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SmoothRepSchur.lean#L68-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SmoothRepSchur.lean#L68-L131

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
variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ G V}

theorem GroundTheory.Automorphic.algebraMap_intertwiningMap_bijective_of_rank_le_aleph0 [ρ.IsIrreducible]
    (hV : Module.rank ℂ V ≤ ℵ₀) :
    Function.Bijective (algebraMap ℂ (Representation.IntertwiningMap ρ ρ)) := by sorry
