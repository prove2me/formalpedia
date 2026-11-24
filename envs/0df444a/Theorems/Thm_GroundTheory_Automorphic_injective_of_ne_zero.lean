-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_injective_of_ne_zero
-- name    : GroundTheory.Automorphic.injective_of_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:13:33.091155+00:00
-- url     : https://prove2.me/theorems/b3509125-8ea7-407f-8d63-ef04696495f3
-- title:
--   Automorphic: injective of ne zero
-- statement:
--   The Automorphic construction uses the injective of ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SmoothRepSchur.lean#L24-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SmoothRepSchur.lean#L24-L26

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

theorem GroundTheory.Automorphic.injective_of_ne_zero [ρ.IsIrreducible] {f : Representation.IntertwiningMap ρ ρ}
    (hf : f ≠ 0) : Function.Injective f := by sorry
