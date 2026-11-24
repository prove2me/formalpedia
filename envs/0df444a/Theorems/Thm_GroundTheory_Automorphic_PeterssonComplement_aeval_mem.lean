-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_PeterssonComplement_aeval_mem
-- name    : GroundTheory.Automorphic.PeterssonComplement.aeval_mem
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:33:03.386171+00:00
-- url     : https://prove2.me/theorems/5357092b-9b57-4cd1-bc07-bf86d26b2370
-- title:
--   Petersson Complement: aeval mem
-- statement:
--   The Petersson Complement construction uses the aeval mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/PeterssonComplement.lean#L75-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/PeterssonComplement.lean#L75-L89

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

theorem GroundTheory.Automorphic.PeterssonComplement.aeval_mem {T : Module.End ℂ V} {Z : Submodule ℂ V} (hZ : ∀ z ∈ Z, T z ∈ Z) (q : ℂ[X]) :
    ∀ z ∈ Z, aeval T q z ∈ Z := by sorry
