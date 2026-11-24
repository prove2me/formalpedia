-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_isSmooth_indRep
-- name    : GroundTheory.Automorphic.isSmooth_indRep
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T10:43:43.355667+00:00
-- url     : https://prove2.me/theorems/f9002b4d-0670-4ddb-8e8b-edac44885ea7
-- title:
--   Automorphic: is Smooth ind Rep
-- statement:
--   The Automorphic construction uses the is Smooth ind Rep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/Induction.lean#L127-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/Induction.lean#L127-L132

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
variable [IsTopologicalGroup G]

theorem GroundTheory.Automorphic.isSmooth_indRep : IsSmooth (indRep H σ) := by sorry
