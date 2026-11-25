-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_PeterssonComplement_map_mem_orthIn
-- name    : GroundTheory.Automorphic.PeterssonComplement.map_mem_orthIn
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:53:40.314397+00:00
-- url     : https://prove2.me/theorems/81589b7f-2e11-4b82-bf79-f152349c17ef
-- title:
--   Petersson Complement: map mem orth In
-- statement:
--   The Petersson Complement construction uses the map mem orth In property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/PeterssonComplement.lean#L148-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/PeterssonComplement.lean#L148-L152

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

theorem GroundTheory.Automorphic.PeterssonComplement.map_mem_orthIn {U : Submodule ℂ V} {A A' : V → V}
    (hA : ∀ x y, inner ℂ (ι (A' x)) (ι y) = inner ℂ (ι x) (ι (A y))) (hU : ∀ u ∈ U, A' u ∈ U)
    {v : V} (hv : v ∈ orthIn ι U) : A v ∈ orthIn ι U := by sorry
