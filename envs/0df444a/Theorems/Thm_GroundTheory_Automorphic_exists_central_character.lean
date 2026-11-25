-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_exists_central_character
-- name    : GroundTheory.Automorphic.exists_central_character
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T10:33:42.787266+00:00
-- url     : https://prove2.me/theorems/5c26d2d3-6555-4f69-9689-09961f136a9d
-- title:
--   Automorphic: exists central character
-- statement:
--   The Automorphic construction uses the exists central character property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SmoothRepSchur.lean#L183-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SmoothRepSchur.lean#L183-L187

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

theorem GroundTheory.Automorphic.exists_central_character (hρ : IsSmooth ρ) [ρ.IsIrreducible] {z : G}
    (hz : z ∈ Submonoid.center G) : ∃ c : ℂ, ∀ v : V, ρ z v = c • v := by sorry
