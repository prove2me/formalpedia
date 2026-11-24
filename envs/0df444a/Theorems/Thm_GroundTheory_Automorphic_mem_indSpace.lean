-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_mem_indSpace
-- name    : GroundTheory.Automorphic.mem_indSpace
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T09:45:31.326207+00:00
-- url     : https://prove2.me/theorems/70741cf5-b5c8-4d74-940e-1a29267af7d1
-- title:
--   Automorphic: mem ind Space
-- statement:
--   The Automorphic construction uses the mem ind Space property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/Induction.lean#L49-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/Induction.lean#L49-L52

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Definitions.Def_GroundTheory_AutomorphicForms_Induction
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
open Set Filter Topology Pointwise
variable {G : Type*} [Group G] [TopologicalSpace G] (H : Subgroup G)
  {W : Type*} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ H W)
variable {H σ}

theorem GroundTheory.Automorphic.mem_indSpace {f : G → W} :
    f ∈ indSpace H σ ↔ (∀ h : H, ∀ g : G, f ((h : G) * g) = σ h (f g)) ∧
      ∃ K : Subgroup G, IsOpen (K : Set G) ∧ ∀ k ∈ K, ∀ g : G, f (g * k) = f g := by sorry
