-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_exists_ne_zero_of_isIrreducible
-- name    : GroundTheory.Automorphic.exists_ne_zero_of_isIrreducible
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:09:43.494701+00:00
-- url     : https://prove2.me/theorems/dffebd70-7e75-4b42-8796-8a201b73e31c
-- title:
--   Automorphic: exists ne zero of is Irreducible
-- statement:
--   The Automorphic construction uses the exists ne zero of is Irreducible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SmoothRepSchur.lean#L15-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SmoothRepSchur.lean#L15-L22

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

theorem GroundTheory.Automorphic.exists_ne_zero_of_isIrreducible [ρ.IsIrreducible] : ∃ v : V, v ≠ 0 := by sorry
