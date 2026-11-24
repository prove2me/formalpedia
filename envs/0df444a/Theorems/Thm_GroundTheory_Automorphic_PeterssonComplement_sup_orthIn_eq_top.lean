-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_PeterssonComplement_sup_orthIn_eq_top
-- name    : GroundTheory.Automorphic.PeterssonComplement.sup_orthIn_eq_top
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:33:03.8548+00:00
-- url     : https://prove2.me/theorems/107de894-0b3b-4cea-85e4-b37eb0cbb29d
-- title:
--   Petersson Complement: sup orth In eq top
-- statement:
--   The Petersson Complement construction uses the sup orth In eq top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/PeterssonComplement.lean#L32-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/PeterssonComplement.lean#L32-L48

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

theorem GroundTheory.Automorphic.PeterssonComplement.sup_orthIn_eq_top (U : Submodule ℂ V)
    (h : ∀ v : V, ∃ W : Submodule ℂ V, FiniteDimensional ℂ W ∧ v ∈ W ∧
      ∀ u ∈ U, ∃ u' ∈ U ⊓ W, ∀ w ∈ W, inner ℂ (ι u) (ι w) = inner ℂ (ι u') (ι w)) :
    U ⊔ orthIn ι U = ⊤ := by sorry
