-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_rank_le_aleph0_of_isSmooth
-- name    : GroundTheory.Automorphic.rank_le_aleph0_of_isSmooth
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:35:18.669438+00:00
-- url     : https://prove2.me/theorems/b04da5c0-49b8-4007-a7ab-39da7a00ddfb
-- title:
--   Automorphic: rank le aleph0 of is Smooth
-- statement:
--   The Automorphic construction uses the rank le aleph0 of is Smooth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SmoothRepSchur.lean#L141-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SmoothRepSchur.lean#L141-L177

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

theorem GroundTheory.Automorphic.rank_le_aleph0_of_isSmooth (hρ : IsSmooth ρ) [ρ.IsIrreducible] :
    Module.rank ℂ V ≤ ℵ₀ := by sorry
