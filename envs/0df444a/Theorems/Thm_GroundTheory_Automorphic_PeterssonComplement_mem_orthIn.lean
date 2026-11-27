-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_PeterssonComplement_mem_orthIn
-- name    : GroundTheory.Automorphic.PeterssonComplement.mem_orthIn
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:53:26.060118+00:00
-- url     : https://prove2.me/theorems/9f8a34d6-aba1-4801-9f78-23e15e443482
-- title:
--   Petersson Complement: mem orth In
-- statement:
--   The Petersson Complement construction uses the mem orth In property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/PeterssonComplement.lean#L22-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/PeterssonComplement.lean#L22-L23

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_PeterssonComplement
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
open GroundTheory.Automorphic.PeterssonComplement
open Polynomial
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ι : V →ₗ[ℂ] H)
variable {ι}

theorem GroundTheory.Automorphic.PeterssonComplement.mem_orthIn {U : Submodule ℂ V} {v : V} :
    v ∈ orthIn ι U ↔ ∀ u ∈ U, inner ℂ (ι u) (ι v) = 0 := by sorry
